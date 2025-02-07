-- Copyright 2018, Data61, CSIRO
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)

-- This module defines the handling of the RISC-V hardware-defined page tables.

module SEL4.Kernel.VSpace.RISCV64 where

import Prelude hiding (Word)
import SEL4.API.Types
import SEL4.API.Failures
import SEL4.API.Failures.RISCV64
import SEL4.Machine.RegisterSet
import SEL4.Machine.RegisterSet.RISCV64 (Register(..))
import SEL4.Machine.Hardware.RISCV64
import SEL4.Model
import SEL4.Object.Structures
import SEL4.Model.StateData.RISCV64
import SEL4.API.InvocationLabels
import SEL4.API.InvocationLabels.RISCV64
import {-# SOURCE #-} SEL4.Object.CNode
import {-# SOURCE #-} SEL4.Object.TCB
import {-# SOURCE #-} SEL4.Kernel.Init
import {-# SOURCE #-} SEL4.Kernel.CSpace

import Data.Bits
import Data.Maybe
import Data.Array
import Data.Word (Word32)

-- The RISC-V-specific invocations are imported with the "ArchInv" prefix. This
-- is necessary to avoid namespace conflicts with the generic invocations.

import SEL4.API.Invocation.RISCV64 as ArchInv

{- Constants -}

-- counting from 0, i.e. number of levels = maxPTLevel + 1 = top-level table
maxPTLevel :: Int
maxPTLevel = 2

ipcBufferSizeBits :: Int
ipcBufferSizeBits = 10

{- Creating a New Address Space -}

copyGlobalMappings :: PPtr PTE -> Kernel ()
copyGlobalMappings newPT = do
    globalPT <- gets (riscvKSGlobalPT . ksArchState)
    let base = ptIndex maxPTLevel pptrBase
    let ptSize = 1 `shiftL` ptTranslationBits -- number of entries in table
    forM_ [base .. ptSize - 1] $ \index -> do
        let offset = PPtr index `shiftL` pteBits
        pte <- getObject $ globalPT + offset
        storePTE (newPT + offset) pte

{- Lookups and Faults -}

{- IPC Buffer Accesses -}

-- physical address of the IPC buffer, if it is accessible
lookupIPCBuffer :: Bool -> PPtr TCB -> Kernel (Maybe (PPtr Word))
lookupIPCBuffer isReceiver thread = do
    bufferPtr <- threadGet tcbIPCBuffer thread
    bufferFrameSlot <- getThreadBufferSlot thread
    bufferCap <- getSlotCap bufferFrameSlot
    case bufferCap of
        ArchObjectCap (FrameCap {capFIsDevice = False, capFBasePtr = basePtr,
                                 capFVMRights = rights, capFSize = sz}) -> do
            let pBits = pageBitsForSize sz
            if (rights == VMReadWrite || not isReceiver && rights == VMReadOnly)
                then do
                    let ptr = basePtr + PPtr (fromVPtr bufferPtr .&. mask pBits)
                    assert (ptr /= 0) "IPC buffer pointer must be non-null"
                    return $ Just ptr
                else return Nothing
        _ -> return Nothing

{- ASID Lookups -}

findVSpaceForASID :: ASID -> KernelF LookupFailure (PPtr PTE)
findVSpaceForASID asid = do
    assert (asid > 0) "ASID 0 is used for objects that are not mapped"
    assert (asid <= snd asidRange) "ASID out of range"
    asidTable <- withoutFailure $ gets (riscvKSASIDTable . ksArchState)
    let poolPtr = asidTable!(asidHighBitsOf asid)
    ASIDPool pool <- case poolPtr of
        Just ptr -> withoutFailure $ getObject ptr
        Nothing -> throw InvalidRoot
    let pm = pool!(asid .&. mask asidLowBits)
    case pm of
        Just ptr -> do
            assert (ptr /= 0) "findVSpaceForASID: found null PD"
            withoutFailure $ checkPTAt ptr
            return ptr
        Nothing -> throw InvalidRoot

findVSpaceForASIDAssert :: ASID -> Kernel (PPtr PTE)
findVSpaceForASIDAssert asid = do
    pm <- findVSpaceForASID asid `catchFailure`
        const (fail "findVSpaceForASIDAssert: pt not found")
    assert (pm .&. mask ptBits == 0)
        "findVSpaceForASIDAssert: pt pointer alignment check"
    checkPTAt pm
    return pm

-- used in proofs only, will be translated to ptable_at.
checkPTAt :: PPtr PTE -> Kernel ()
checkPTAt _ = return ()


{- Locating Page Table Slots -}

isPageTablePTE :: PTE -> Bool
isPageTablePTE (PageTablePTE {}) = True
isPageTablePTE _ = False

getPPtrFromHWPTE :: PTE -> PPtr PTE
getPPtrFromHWPTE pte = ptrFromPAddr (ptePPN pte `shiftL` ptBits)

-- how many bits there are left to be translated at a given level
-- (0 = bottom level)
ptBitsLeft :: Int -> Int
ptBitsLeft level = ptTranslationBits * level + pageBits

-- compute index into a page table from vPtr at given level
ptIndex :: Int -> VPtr -> Word
ptIndex level vPtr =
    (fromVPtr vPtr `shiftR` ptBitsLeft level) .&. mask ptTranslationBits

-- compute slot ptr inside the table ptPtr at given level for a vPtr
ptSlotIndex :: Int -> PPtr PTE -> VPtr -> PPtr PTE
ptSlotIndex level ptPtr vPtr =
    ptPtr + PPtr (ptIndex level vPtr `shiftL` pteBits)

-- Look up the pte in the table ptPtr at given level with index computed from
-- vPtr for that level.
pteAtIndex :: Int -> PPtr PTE -> VPtr -> Kernel PTE
pteAtIndex level ptPtr vPtr = getObject (ptSlotIndex level ptPtr vPtr)

-- We are counting levels down instead of up, i.e. level maxPTLevel is the
-- top-level page table, and level 0 is the bottom level that contains only
-- pages or invalid entries.
lookupPTSlotFromLevel :: Int -> PPtr PTE -> VPtr -> Kernel (Int, PPtr PTE)
lookupPTSlotFromLevel level ptPtr vPtr = do
    pte <- pteAtIndex level ptPtr vPtr
    let ptr = getPPtrFromHWPTE pte
    if isPageTablePTE pte && level > 0
        then lookupPTSlotFromLevel (level-1) ptr vPtr
        else return (ptBitsLeft level, ptr)

-- lookupPTSlot walks the page table and returns a pointer to the slot that maps
-- a given virtual address, together with the number of bits left to translate,
-- indicating the size of the frame.
lookupPTSlot :: PPtr PTE -> VPtr -> Kernel (Int, PPtr PTE)
lookupPTSlot = lookupPTSlotFromLevel maxPTLevel


{- Handling Faults -}

handleVMFault :: PPtr TCB -> VMFaultType -> KernelF Fault ()
handleVMFault thread f = do
    w <- withoutFailure $ doMachineOp read_sbadaddr
    let addr = VPtr w
    case f of
        RISCVLoadPageFault -> throw $ loadf addr
        RISCVLoadAccessFault -> throw $ loadf addr
        RISCVStorePageFault -> throw $ storef addr
        RISCVStoreAccessFault -> throw $ storef addr
        RISCVInstructionPageFault -> do
            withoutFailure $ setPC
            throw $ instrf addr
        RISCVInstructionAccessFault ->  do
            withoutFailure $ setPC
            throw $ instrf addr
        _ -> error "Invalid VM fault type"
    where loadf a = ArchFault $ VMFault a [0, vmFaultTypeFSR RISCVLoadAccessFault]
          storef a = ArchFault $ VMFault a [0, vmFaultTypeFSR RISCVStoreAccessFault]
          instrf a = ArchFault $ VMFault a [1, vmFaultTypeFSR RISCVInstructionAccessFault]
          setPC = do
              faultip <- asUser thread $ getRegister (Register FaultIP)
              asUser thread $ setRegister (Register NextIP) faultip

{- Unmapping and Deletion -}

-- When a capability backing a virtual memory mapping is deleted, or when an
-- explicit request is made to remove a mapping, the kernel must locate the
-- corresponding entries in the page table or ASID table and remove them. It is
-- also necessary to flush the removed mappings from the hardware caches.

{- Deleting an ASID Pool -}

deleteASIDPool :: ASID -> PPtr ASIDPool -> Kernel ()
deleteASIDPool base ptr = do
    assert (base .&. mask asidLowBits == 0)
        "ASID pool's base must be aligned"
    asidTable <- gets (riscvKSASIDTable . ksArchState)
    when (asidTable ! (asidHighBitsOf base) == Just ptr) $ do
        ASIDPool pool <- getObject ptr
        let asidTable' = asidTable//[(asidHighBitsOf base, Nothing)]
        modify (\s -> s {
            ksArchState = (ksArchState s) { riscvKSASIDTable = asidTable' }})
        tcb <- getCurThread
        setVMRoot tcb

{- Deleting an Address Space -}

deleteASID :: ASID -> PPtr PTE -> Kernel ()
deleteASID asid pt = do
    asidTable <- gets (riscvKSASIDTable . ksArchState)
    case asidTable!(asidHighBitsOf asid) of
        Nothing -> return ()
        Just poolPtr -> do
            ASIDPool pool <- getObject poolPtr
            when (pool!(asid .&. mask asidLowBits) == Just pt) $ do
                doMachineOp $ hwASIDFlush (fromASID asid)
                let pool' = pool//[(asid .&. mask asidLowBits, Nothing)]
                setObject poolPtr $ ASIDPool pool'
                tcb <- getCurThread
                setVMRoot tcb

{- Deleting a Page Table -}

-- Difference to lookupPTSlotFromLevel is that we are given a target page table
-- the slot should be in. If we don't find that page table during the walk, we
-- will throw an exception which is later ignored, in the sense that it is used
-- for early return + do nothing.
-- Returns only slots with pageTablePTEs
lookupPTFromLevel :: Int -> PPtr PTE -> VPtr -> PPtr PTE -> KernelF LookupFailure (PPtr PTE)
lookupPTFromLevel level ptPtr vPtr targetPtPtr = do
    unless (0 < level) $ throw InvalidRoot
    pte <- withoutFailure $ pteAtIndex level ptPtr vPtr
    unless (isPageTablePTE pte) $ throw InvalidRoot
    let ptr = getPPtrFromHWPTE pte
    if ptr == targetPtPtr
        then return $ ptSlotIndex (level-1) ptr vPtr
        else lookupPTFromLevel (level-1) ptr vPtr targetPtPtr

unmapPageTable :: ASID -> VPtr -> PPtr PTE -> Kernel ()
unmapPageTable asid vaddr pt = ignoreFailure $ do
    topLevelPT <- findVSpaceForASID asid
    ptSlot <- lookupPTFromLevel maxPTLevel topLevelPT vaddr pt
    withoutFailure $ storePTE ptSlot InvalidPTE
    withoutFailure $ doMachineOp sfence

{- Unmapping a Frame -}

-- If the previous PTE is not a page pointing at the same address we are
-- trying to unmap, the information is outdated and the operation should be ignored.
checkMappingPPtr :: PPtr Word -> PTE -> KernelF LookupFailure ()
checkMappingPPtr pptr pte =
    case pte of
        PagePTE { ptePPN = ppn } ->
            unless (ptrFromPAddr ppn == pptr) $ throw InvalidRoot
        _ -> throw InvalidRoot

unmapPage :: VMPageSize -> ASID -> VPtr -> PPtr Word -> Kernel ()
unmapPage size asid vptr pptr = ignoreFailure $ do
    vspace <- findVSpaceForASID asid
    (bitsLeft, slot) <- withoutFailure $ lookupPTSlot vspace vptr
    unless (bitsLeft == pageBitsForSize size) $ throw InvalidRoot
    pte <- withoutFailure $ getObject slot
    checkMappingPPtr pptr pte
    withoutFailure $ storePTE slot InvalidPTE
    withoutFailure $ doMachineOp sfence

{- Address Space Switching -}

setVMRoot :: PPtr TCB -> Kernel ()
setVMRoot tcb = do
    threadRootSlot <- getThreadVSpaceRoot tcb
    threadRoot <- getSlotCap threadRootSlot
    catchFailure
        (case threadRoot of
            ArchObjectCap (PageTableCap {
                    capPTMappedAddress = Just (asid, _),
                    capPTBasePtr = pt }) -> do
                pt' <- findVSpaceForASID asid
                when (pt /= pt') $ throw InvalidRoot
                withoutFailure $ doMachineOp $
                    setVSpaceRoot (addrFromPPtr pt) (fromASID asid)
            _ -> throw InvalidRoot)
        (\_ -> do
            globalPT <- gets (riscvKSGlobalPT . ksArchState)
            doMachineOp $ setVSpaceRoot (addrFromKPPtr globalPT) 0)


{- Helper Functions -}

checkValidIPCBuffer :: VPtr -> Capability -> KernelF SyscallError ()
checkValidIPCBuffer vptr (ArchObjectCap (FrameCap {capFIsDevice = False})) = do
    when (vptr .&. mask ipcBufferSizeBits /= 0) $ throw AlignmentError
    return ()
checkValidIPCBuffer _ _ = throw IllegalOperation

isValidVTableRoot :: Capability -> Bool
isValidVTableRoot
    (ArchObjectCap (PageTableCap { capPTMappedAddress = Just _ })) = True
isValidVTableRoot _ = False

maskVMRights :: VMRights -> CapRights -> VMRights
maskVMRights r m = case (r, capAllowRead m, capAllowWrite m) of
    (VMReadOnly, True, _) -> VMReadOnly
    (VMReadWrite, True, False) -> VMReadOnly
    (VMReadWrite, True, True) -> VMReadWrite
    _ -> VMKernelOnly


{- Decoding RISC-V Invocations -}

attribsFromWord :: Word -> VMAttributes
attribsFromWord w = VMAttributes { riscvExecuteNever = w `testBit` 0 }

makeUserPTE :: PAddr -> Bool -> VMRights -> PTE
makeUserPTE baseAddr executable rights =
    PagePTE {
        ptePPN = baseAddr `shiftR` pageBits,
        pteGlobal = False,
        pteUser = rights /= VMKernelOnly,
        pteExecute = executable,
        pteRights = rights }

checkVPAlignment :: VMPageSize -> VPtr -> KernelF SyscallError ()
checkVPAlignment sz w =
    unless (w .&. mask (pageBitsForSize sz) == 0) $ throw AlignmentError

checkSlot :: PPtr PTE -> (PTE -> Bool) -> KernelF SyscallError ()
checkSlot slot test = do
    pte <- withoutFailure $ getObject slot
    unless (test pte) $ throw DeleteFirst

decodeRISCVFrameInvocationMap :: PPtr CTE -> ArchCapability -> VPtr -> Word ->
    Word -> Capability -> KernelF SyscallError ArchInv.Invocation
decodeRISCVFrameInvocationMap cte cap vptr rightsMask attr vspaceCap = do
    when (isJust $ capFMappedAddress cap) $ throw $ InvalidCapability 0
    (vspace,asid) <- case vspaceCap of
        ArchObjectCap (PageTableCap {
                capPTMappedAddress = Just (asid, _),
                capPTBasePtr = vspace })
            -> return (vspace, asid)
        _ -> throw $ InvalidCapability 1
    vspaceCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
    when (vspaceCheck /= vspace) $ throw $ InvalidCapability 1
    let pgBits = pageBitsForSize $ capFSize cap
    let vtop = vptr + (bit pgBits - 1)
    when (vtop >= pptrUserTop) $ throw $ InvalidArgument 0
    checkVPAlignment (capFSize cap) vptr
    (bitsLeft, slot) <- withoutFailure $ lookupPTSlot vspace vptr
    unless (bitsLeft == pgBits) $ throw $
        FailedLookup False $ MissingCapability bitsLeft
    checkSlot slot (\pte ->  pte == InvalidPTE)
    let vmRights = maskVMRights (capFVMRights cap) $ rightsFromWord rightsMask
    let framePAddr = addrFromPPtr (capFBasePtr cap)
    let exec = not $ riscvExecuteNever (attribsFromWord attr)
    return $ InvokePage $ PageMap {
        pageMapCap = ArchObjectCap $ cap { capFMappedAddress = Just (asid,vptr) },
        pageMapCTSlot = cte,
        pageMapEntries = (makeUserPTE framePAddr exec vmRights, slot) }

decodeRISCVFrameInvocationRemap :: PPtr CTE -> ArchCapability -> Word ->
    Word -> Capability -> KernelF SyscallError ArchInv.Invocation
decodeRISCVFrameInvocationRemap cte cap rightsMask attr vspaceCap = do
    (vspace,asid) <- case vspaceCap of
        ArchObjectCap (PageTableCap {
                capPTMappedAddress = Just (asid, _),
                capPTBasePtr = vspace })
            -> return (vspace, asid)
        _ -> throw $ InvalidCapability 1
    (asid',vaddr) <- case capFMappedAddress cap of
        Just v -> return v
        _ -> throw $ InvalidCapability 0
    vspaceCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
    when (vspaceCheck /= vspace || asid /= asid') $ throw $ InvalidCapability 1
    checkVPAlignment (capFSize cap) vaddr
    (bitsLeft, slot) <- withoutFailure $ lookupPTSlot vspace vaddr
    let pgBits = pageBitsForSize $ capFSize cap
    unless (bitsLeft == pgBits) $ throw $
        FailedLookup False $ MissingCapability bitsLeft
    checkSlot slot (not . isPageTablePTE)
    let vmRights = maskVMRights (capFVMRights cap) $ rightsFromWord rightsMask
    let framePAddr = addrFromPPtr (capFBasePtr cap)
    let exec = not $ riscvExecuteNever (attribsFromWord attr)
    return $ InvokePage $ PageRemap {
        pageRemapEntries = (makeUserPTE framePAddr exec vmRights, slot) }


decodeRISCVFrameInvocation :: Word -> [Word] -> PPtr CTE ->
                   ArchCapability -> [(Capability, PPtr CTE)] ->
                   KernelF SyscallError ArchInv.Invocation

decodeRISCVFrameInvocation label args cte (cap@FrameCap {}) extraCaps =
    case (invocationType label, args, extraCaps) of
        (ArchInvocationLabel RISCVPageMap, vaddr:rightsMask:attr:_, (vspaceCap,_):_) -> do
            decodeRISCVFrameInvocationMap cte cap (VPtr vaddr) rightsMask attr vspaceCap
        (ArchInvocationLabel RISCVPageMap, _, _) -> throw TruncatedMessage
        (ArchInvocationLabel RISCVPageRemap, rightsMask:attr:_, (vspaceCap,_):_) -> do
            decodeRISCVFrameInvocationRemap cte cap rightsMask attr vspaceCap
        (ArchInvocationLabel RISCVPageRemap, _, _) -> throw TruncatedMessage
        (ArchInvocationLabel RISCVPageUnmap, _, _) ->
            return $ InvokePage $ PageUnmap {
                pageUnmapCap = cap,
                pageUnmapCapSlot = cte }
        (ArchInvocationLabel RISCVPageGetAddress, _, _) ->
            return $ InvokePage $ PageGetAddr (capFBasePtr cap)
        _ -> throw IllegalOperation
decodeRISCVFrameInvocation _ _ _ _ _ = fail "Unreachable"


decodeRISCVPageTableInvocationMap :: PPtr CTE -> ArchCapability -> VPtr ->
    Word -> Capability -> KernelF SyscallError ArchInv.Invocation
decodeRISCVPageTableInvocationMap cte cap vptr attr vspaceCap = do
    when (isJust $ capPTMappedAddress cap) $ throw $ InvalidCapability 0
    (vspace,asid) <- case vspaceCap of
        ArchObjectCap (PageTableCap {
                 capPTMappedAddress = Just (asid,_),
                 capPTBasePtr = vspace })
            -> return (vspace,asid)
        _ -> throw $ InvalidCapability 1
    when (vptr >= pptrUserTop) $ throw $ InvalidArgument 0
    vspaceCheck <- lookupErrorOnFailure False $ findVSpaceForASID asid
    when (vspaceCheck /= vspace) $ throw $ InvalidCapability 1
    (bitsLeft, slot) <- withoutFailure $ lookupPTSlot vspace vptr
    oldPTE <- withoutFailure $ getObject slot
    when (bitsLeft == pageBits || oldPTE /= InvalidPTE) $ throw DeleteFirst
    let pte = PageTablePTE {
            ptePPN = addrFromPPtr (capPTBasePtr cap) `shiftR` pageBits,
            pteGlobal = False,
            pteUser = False }
    return $ InvokePageTable $ PageTableMap {
        ptMapCap = ArchObjectCap $ cap { capPTMappedAddress = Just (asid, vptr) },
        ptMapCTSlot = cte,
        ptMapPTE = pte,
        ptMapPTSlot = slot }

decodeRISCVPageTableInvocation :: Word -> [Word] -> PPtr CTE ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeRISCVPageTableInvocation label args cte cap@(PageTableCap {}) extraCaps =
   case (invocationType label, args, extraCaps) of
        (ArchInvocationLabel RISCVPageTableMap, vaddr:attr:_, (vspaceCap,_):_) -> do
            decodeRISCVPageTableInvocationMap cte cap (VPtr vaddr) attr vspaceCap
        (ArchInvocationLabel RISCVPageTableMap, _, _) -> throw TruncatedMessage
        (ArchInvocationLabel RISCVPageTableUnmap, _, _) -> do
            cteVal <- withoutFailure $ getCTE cte
            final <- withoutFailure $ isFinalCapability cteVal
            unless final $ throw RevokeFirst
            return $ InvokePageTable $ PageTableUnmap {
                ptUnmapCap = cap,
                ptUnmapCapSlot = cte }
        _ -> throw IllegalOperation
decodeRISCVPageTableInvocation _ _ _ _ _ = fail "Unreachable"


decodeRISCVASIDControlInvocation :: Word -> [Word] ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation

decodeRISCVASIDControlInvocation label args ASIDControlCap extraCaps =
    case (invocationType label, args, extraCaps) of
        (ArchInvocationLabel RISCVASIDControlMakePool, index:depth:_,
                        (untyped,parentSlot):(croot,_):_) -> do
            asidTable <- withoutFailure $ gets (riscvKSASIDTable . ksArchState)
            let free = filter (\(x,y) -> x <= (1 `shiftL` asidHighBits) - 1 && isNothing y) $ assocs asidTable
            when (null free) $ throw DeleteFirst
            let base = (fst $ head free) `shiftL` asidLowBits
            let pool = makeObject :: ASIDPool
            frame <- case untyped of
                UntypedCap { capIsDevice = False } | capBlockSize untyped == objBits pool -> do
                    ensureNoChildren parentSlot
                    return $ capPtr untyped
                _ -> throw $ InvalidCapability 1
            destSlot <- lookupTargetSlot croot (CPtr index) (fromIntegral depth)
            ensureEmptySlot destSlot
            return $ InvokeASIDControl $ MakePool {
                makePoolFrame = frame,
                makePoolSlot = destSlot,
                makePoolParent = parentSlot,
                makePoolBase = base }
        (ArchInvocationLabel RISCVASIDControlMakePool, _, _) -> throw TruncatedMessage
        _ -> throw IllegalOperation
decodeRISCVASIDControlInvocation _ _ _ _ = fail "Unreachable"


decodeRISCVASIDPoolInvocation :: Word ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation

decodeRISCVASIDPoolInvocation label cap@(ASIDPoolCap {}) extraCaps =
    case (invocationType label, extraCaps) of
        (ArchInvocationLabel RISCVASIDPoolAssign, (vspaceCap,vspaceCapSlot):_) ->
            case vspaceCap of
                ArchObjectCap (PageTableCap { capPTMappedAddress = Nothing })
                  -> do
                    asidTable <- withoutFailure $ gets (riscvKSASIDTable . ksArchState)
                    let base = capASIDBase cap
                    let poolPtr = asidTable!(asidHighBitsOf base)
                    when (isNothing poolPtr) $ throw $ FailedLookup False InvalidRoot
                    let Just p = poolPtr
                    when (p /= capASIDPool cap) $ throw $ InvalidCapability 0
                    ASIDPool pool <- withoutFailure $ getObject $ p
                    let free = filter (\(x,y) -> x <=  (1 `shiftL` asidLowBits) - 1
                                                 && x + base /= 0 && isNothing y) $ assocs pool
                    when (null free) $ throw DeleteFirst
                    let asid = fst $ head free
                    return $ InvokeASIDPool $ Assign {
                        assignASID = asid + base,
                        assignASIDPool = capASIDPool cap,
                        assignASIDCTSlot = vspaceCapSlot }
                _ -> throw $ InvalidCapability 1
        (ArchInvocationLabel RISCVASIDPoolAssign, _) -> throw TruncatedMessage
        _ -> throw IllegalOperation
decodeRISCVASIDPoolInvocation _ _ _ = fail "Unreachable"


decodeRISCVMMUInvocation :: Word -> [Word] -> CPtr -> PPtr CTE ->
        ArchCapability -> [(Capability, PPtr CTE)] ->
        KernelF SyscallError ArchInv.Invocation
decodeRISCVMMUInvocation label args _ cte cap@(FrameCap {}) extraCaps =
    decodeRISCVFrameInvocation label args cte cap extraCaps
decodeRISCVMMUInvocation label args _ cte cap@(PageTableCap {}) extraCaps =
    decodeRISCVPageTableInvocation label args cte cap extraCaps
decodeRISCVMMUInvocation label args _ _ cap@(ASIDControlCap {}) extraCaps =
    decodeRISCVASIDControlInvocation label args cap extraCaps
decodeRISCVMMUInvocation label _ _ _ cap@(ASIDPoolCap {}) extraCaps =
    decodeRISCVASIDPoolInvocation label cap extraCaps


{- Invocation Implementations -}

performPageTableInvocation :: PageTableInvocation -> Kernel ()
performPageTableInvocation (PageTableMap cap ctSlot pte ptSlot) = do
    updateCap ctSlot cap
    storePTE ptSlot pte
    doMachineOp sfence

performPageTableInvocation (PageTableUnmap cap slot) = do
    case capPTMappedAddress cap of
        Just (asid, vaddr) -> do
            let ptr = capPTBasePtr cap
            unmapPageTable asid vaddr ptr
            let slots = [ptr, ptr + bit pteBits .. ptr + bit ptBits - 1]
            mapM_ (flip storePTE InvalidPTE) slots
        _ -> return ()
    ArchObjectCap cap <- getSlotCap slot
    updateCap slot (ArchObjectCap $ cap { capPTMappedAddress = Nothing })


performPageInvocation :: PageInvocation -> Kernel ()
performPageInvocation (PageMap cap ctSlot (pte,slot)) = do
    updateCap ctSlot cap
    storePTE slot pte
    doMachineOp sfence

performPageInvocation (PageRemap (pte,slot)) = do
    storePTE slot pte
    doMachineOp sfence

performPageInvocation (PageUnmap cap ctSlot) = do
    case capFMappedAddress cap of
        Just (asid, vaddr) -> unmapPage (capFSize cap) asid vaddr (capFBasePtr cap)
        _ -> return ()
    ArchObjectCap cap <- getSlotCap ctSlot
    updateCap ctSlot (ArchObjectCap $ cap { capFMappedAddress = Nothing })

performPageInvocation (PageGetAddr ptr) = do
    let paddr = fromPAddr $ addrFromPPtr ptr
    ct <- getCurThread
    msgTransferred <- setMRs ct Nothing [paddr]
    msgInfo <- return $ MI {
            msgLength = msgTransferred,
            msgExtraCaps = 0,
            msgCapsUnwrapped = 0,
            msgLabel = 0 }
    setMessageInfo ct msgInfo


performASIDControlInvocation :: ASIDControlInvocation -> Kernel ()
performASIDControlInvocation (MakePool frame slot parent base) = do
    deleteObjects frame pageBits
    pcap <- getSlotCap parent
    updateFreeIndex parent (maxFreeIndex (capBlockSize pcap))
    placeNewObject frame (makeObject :: ASIDPool) 0
    let poolPtr = PPtr $ fromPPtr frame
    cteInsert (ArchObjectCap $ ASIDPoolCap poolPtr base) parent slot
    assert (base .&. mask asidLowBits == 0)
        "ASID pool's base must be aligned"
    asidTable <- gets (riscvKSASIDTable . ksArchState)
    let asidTable' = asidTable//[(asidHighBitsOf base, Just poolPtr)]
    modify (\s -> s {
        ksArchState = (ksArchState s) { riscvKSASIDTable = asidTable' }})


performASIDPoolInvocation :: ASIDPoolInvocation -> Kernel ()
performASIDPoolInvocation (Assign asid poolPtr ctSlot) = do
    oldcap <- getSlotCap ctSlot
    let ArchObjectCap cap = oldcap
    updateCap ctSlot (ArchObjectCap $ cap { capPTMappedAddress = Just (asid,0) })
    copyGlobalMappings (capPTBasePtr cap)
    ASIDPool pool <- getObject poolPtr
    let pool' = pool//[(asid .&. mask asidLowBits, Just $ capPTBasePtr cap)]
    setObject poolPtr $ ASIDPool pool'

performRISCVMMUInvocation :: ArchInv.Invocation -> KernelP [Word]
performRISCVMMUInvocation i = withoutPreemption $ do
    case i of
        InvokePageTable oper -> performPageTableInvocation oper
        InvokePage oper -> performPageInvocation oper
        InvokeASIDControl oper -> performASIDControlInvocation oper
        InvokeASIDPool oper -> performASIDPoolInvocation oper
    return $ []

{- Simulator Support -}

storePTE :: PPtr PTE -> PTE -> Kernel ()
storePTE slot pte = do
    setObject slot pte
-- No simulator support currently available for RISCV, but this would be the
-- hook for PTEs:
-- doMachineOp $ storeWordVM (PPtr $ fromPPtr slot) $ wordFromPTE pte


{- Unimplemented Boot Code Stubs -}

mapKernelWindow  :: Kernel ()
mapKernelWindow = error "boot code unimplemented"

activateGlobalVSpace :: Kernel ()
activateGlobalVSpace = error "boot code unimplemented"

createIPCBufferFrame :: Capability -> VPtr -> KernelInit Capability
createIPCBufferFrame = error "boot code unimplemented"

createBIFrame :: Capability -> VPtr -> Word32 -> Word32 -> KernelInit Capability
createBIFrame = error "boot code unimplemented"

createFramesOfRegion :: Capability -> Region -> Bool -> KernelInit ()
createFramesOfRegion = error "boot code unimplemented"

createITPDPTs :: Capability -> VPtr -> VPtr -> KernelInit Capability
createITPDPTs  = error "boot code unimplemented"

writeITPDPTs :: Capability -> Capability -> KernelInit ()
writeITPDPTs  = error "boot code unimplemented"

createITASIDPool :: Capability -> KernelInit Capability
createITASIDPool  = error "boot code unimplemented"

writeITASIDPool :: Capability -> Capability -> Kernel ()
writeITASIDPool  = error "boot code unimplemented"

createDeviceFrames :: Capability -> KernelInit ()
createDeviceFrames  = error "boot code unimplemented"

vptrFromPPtr :: PPtr a -> KernelInit VPtr
vptrFromPPtr  = error "boot code unimplemented"
