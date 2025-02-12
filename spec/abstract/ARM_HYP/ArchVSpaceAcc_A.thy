(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
Accessor functions for architecture specific parts of the specification.
*)

chapter "Accessing the ARM VSpace"

theory ArchVSpaceAcc_A
imports "../KHeap_A"
begin

context Arch begin global_naming ARM_A

text \<open>
  This part of the specification is fairly concrete as the machine architecture
  is visible to the user in seL4 and therefore needs to be described.
  The abstraction compared to the implementation is in the data types for
  kernel objects. The interface which is rich in machine details remains the same.
\<close>

section "Encodings"

text \<open>The high bits of a virtual ASID.\<close>
definition
  asid_high_bits_of :: "asid \<Rightarrow> 7 word" where
  "asid_high_bits_of asid \<equiv> ucast (asid >> asid_low_bits)"


section "Kernel Heap Accessors"

text \<open>Manipulate ASID pools, page directories and page tables in the kernel
heap.\<close>
definition
  get_asid_pool :: "obj_ref \<Rightarrow> (10 word \<rightharpoonup> obj_ref,'z::state_ext) s_monad" where
  "get_asid_pool ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (ASIDPool pool) \<Rightarrow> return pool
                 | _ \<Rightarrow> fail)
   od"

definition
  set_asid_pool :: "obj_ref \<Rightarrow> (10 word \<rightharpoonup> obj_ref) \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "set_asid_pool ptr pool \<equiv> set_object ptr (ArchObj (arch_kernel_obj.ASIDPool pool))"

definition
  get_vcpu :: "obj_ref \<Rightarrow> (vcpu,'z::state_ext) s_monad" where
  "get_vcpu ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (VCPU v) \<Rightarrow> return v
                 | _ \<Rightarrow> fail)
   od"

definition
  set_vcpu :: "obj_ref \<Rightarrow> vcpu \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "set_vcpu ptr vcpu \<equiv> set_object ptr (ArchObj (VCPU vcpu))"

definition
  get_pd :: "obj_ref \<Rightarrow> (11 word \<Rightarrow> pde,'z::state_ext) s_monad" where
  "get_pd ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (PageDirectory pd) \<Rightarrow> return pd
                 | _ \<Rightarrow> fail)
   od"

definition
  set_pd :: "obj_ref \<Rightarrow> (11 word \<Rightarrow> pde) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_pd ptr pd \<equiv> set_object ptr (ArchObj (PageDirectory pd))"

definition
  set_current_pd :: "paddr \<Rightarrow> unit machine_monad"
where
  "set_current_pd pd \<equiv> setCurrentPDPL2 pd"

text \<open>The following function takes a pointer to a PDE in kernel memory
  and returns the actual PDE.\<close>
definition
  get_pde :: "obj_ref \<Rightarrow> (pde,'z::state_ext) s_monad" where
  "get_pde ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask pd_bits);
     offset \<leftarrow> return ((ptr && mask pd_bits) >> pde_bits);
     pd \<leftarrow> get_pd base;
     return $ pd (ucast offset)
   od"

definition
  store_pde :: "obj_ref \<Rightarrow> pde \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_pde p pde \<equiv> do
    base \<leftarrow> return (p && ~~mask pd_bits);
    offset \<leftarrow> return ((p && mask pd_bits) >> pde_bits);
    pd \<leftarrow> get_pd base;
    pd' \<leftarrow> return $ pd (ucast offset := pde);
    set_pd base pd'
  od"


definition
  get_pt :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pte,'z::state_ext) s_monad" where
  "get_pt ptr \<equiv> do
     kobj \<leftarrow> get_object ptr;
     (case kobj of ArchObj (PageTable pt) \<Rightarrow> return pt
                 | _ \<Rightarrow> fail)
   od"

definition
  set_pt :: "obj_ref \<Rightarrow> (9 word \<Rightarrow> pte) \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "set_pt ptr pt \<equiv> set_object ptr (ArchObj (PageTable pt))"

text \<open>The following function takes a pointer to a PTE in kernel memory
  and returns the actual PTE.\<close>
definition
  get_pte :: "obj_ref \<Rightarrow> (pte,'z::state_ext) s_monad" where
  "get_pte ptr \<equiv> do
     base \<leftarrow> return (ptr && ~~mask pt_bits);
     offset \<leftarrow> return ((ptr && mask pt_bits) >> pte_bits);
     pt \<leftarrow> get_pt base;
     return $ pt (ucast offset)
   od"

definition
  store_pte :: "obj_ref \<Rightarrow> pte \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "store_pte p pte \<equiv> do
    base \<leftarrow> return (p && ~~mask pt_bits);
    offset \<leftarrow> return ((p && mask pt_bits) >> pte_bits);
    pt \<leftarrow> get_pt base;
    pt' \<leftarrow> return $ pt (ucast offset := pte);
    set_pt base pt'
  od"


section "Basic Operations"

text \<open>The kernel window is mapped into every virtual address space from the
@{term kernel_base} pointer upwards. This function copies the mappings which
create the kernel window into a new page directory object.\<close>
definition
copy_global_mappings :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
"copy_global_mappings new_pd \<equiv> return ()"
(*do
    global_pt \<leftarrow> gets (arm_global_pt \<circ> arch_state);
    pd_size \<leftarrow> return (1 << pd_bits);
    offset \<leftarrow> return (pd_size - (1 << pde_bits));
    store_pde (new_pd + offset) (PageTablePDE (addrFromPPtr global_pt))
od*)


text \<open>Walk the page directories and tables in software.\<close>

text \<open>The following function takes a page-directory reference as well as
  a virtual address and then computes a pointer to the PDE in kernel memory\<close>
definition
lookup_pd_slot :: "word32 \<Rightarrow> vspace_ref \<Rightarrow> word32" where
"lookup_pd_slot pd vptr \<equiv>
    let pd_index = vptr >> (pageBits + pt_bits - pte_bits) \<comment> \<open>ARMHYP\<close>
    in pd + (pd_index << pde_bits)"

text \<open>The following function takes a page-directory reference as well as
  a virtual address and then computes a pointer to the PTE in kernel memory.
  Note that the function fails if the virtual address is mapped on a section or
  super section.\<close>
definition
lookup_pt_slot :: "word32 \<Rightarrow> vspace_ref \<Rightarrow> (word32,'z::state_ext) lf_monad" where
"lookup_pt_slot pd vptr \<equiv> doE
    pd_slot \<leftarrow> returnOk (lookup_pd_slot pd vptr);
    pde \<leftarrow> liftE $ get_pde pd_slot;
    (case pde of
          PageTablePDE ptab \<Rightarrow>   (doE
            pt \<leftarrow> returnOk (ptrFromPAddr ptab);
            pt_index \<leftarrow> returnOk ((vptr >> pageBits) && mask (pt_bits - pte_bits));
            pt_slot \<leftarrow> returnOk (pt + (pt_index << pte_bits));
            returnOk pt_slot
          odE)
        | _ \<Rightarrow> throwError $ MissingCapability 21)
odE"


text \<open>A non-failing version of @{const lookup_pt_slot} when the pd is already known\<close>
definition
  lookup_pt_slot_no_fail :: "word32 \<Rightarrow> vspace_ref \<Rightarrow> word32"
where
  "lookup_pt_slot_no_fail pt vptr \<equiv>
     let pt_index = ((vptr >> pageBits) && mask (pt_bits - pte_bits))
     in pt + (pt_index << pte_bits)"

end

end
