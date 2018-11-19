theory SchematicRewrite
imports
  Lib.Lib
begin

lemma magic:
  "\<lbrakk>P s; s = t\<rbrakk> \<Longrightarrow> P t"
  by auto

lemma prod1:
  "x = (a, b) \<Longrightarrow> fst x = a"
  by fastforce

lemma prod2:
  "x = (a, b) \<Longrightarrow> snd x = b"
  by fastforce

lemma opt:
  "x = Some y \<Longrightarrow> the x = y"
  by fastforce

lemma list_shred0:
  "xs = y # ys \<Longrightarrow> xs ! 0 = y"
  by fastforce

lemma list_shred1:
  "xs = y0 # y1 # ys \<Longrightarrow> xs ! 1 = y1"
  by fastforce

lemma list_shred2:
  "xs = y0 # y1 # y2 # ys \<Longrightarrow> xs ! 2 = y2"
  by fastforce

lemmas shred = prod1 prod2 opt

lemma thing:
  "\<lbrakk>A; B \<longrightarrow> C; A \<longrightarrow> B\<rbrakk> \<Longrightarrow> C"
  by auto

lemma test1:
  "P (fst x) \<Longrightarrow> P (fst x)"
  apply (erule thing)
   apply (cases x)
   apply (intro impI)
   apply clarsimp
   apply (erule_tac t=a in magic)
   apply (solves \<open>auto intro!: shred\<close>)
  apply fastforce
  done

lemma test2:
  "P (fst (snd x)) \<Longrightarrow> P (fst (snd x))"
  apply (erule thing)
   apply (cases x)
   apply (intro impI)
   apply clarsimp
   apply (erule_tac t=b in magic)
   apply (solves \<open>auto intro!: shred\<close>)
   by fastforce

method shredder_aux for n :: nat = (
  (match (n) in "0 :: nat" \<Rightarrow> \<open>(*print_term "failed",*) fail\<close>
              \<bar> "Suc n' :: nat" for n' \<Rightarrow> \<open>
    (assumption, print_term "solved by asm") |
    ((*print_term "option",*) rule opt, solves \<open>shredder_aux n'\<close>) |
    ((*print_term "left",*) rule prod1, solves \<open>shredder_aux n'\<close>) |
    ((*print_term "right",*) rule prod2, solves \<open>shredder_aux n'\<close>) |
    ((*print_term "right",*) rule list_shred0, solves \<open>shredder_aux n'\<close>) |
    ((*print_term "right",*) rule list_shred1, solves \<open>shredder_aux n'\<close>) |
    ((*print_term "right",*) rule list_shred2, solves \<open>shredder_aux n'\<close>)
  \<close>)
)

method shredder = (shredder_aux "Suc (Suc (Suc (Suc (Suc 0))))")

lemma test:
  "\<lbrakk>f x = Some y\<rbrakk> \<Longrightarrow> y = (inv Some) (f x)"
  apply clarsimp
  done

lemma test':
  "\<lbrakk>x = (a, b)\<rbrakk> \<Longrightarrow> b = (inv (Pair a)) x"
  apply clarsimp
  apply (subst inv_into_f_f)
    apply (rule inj_Pair)
  by auto

lemma test3:
  "P (fst (snd (fst (fst x)))) \<Longrightarrow> P (fst (snd (fst (fst x))))"
  apply (erule thing)
   apply (cases x)
   apply (intro impI)
   apply clarsimp
   apply (erule_tac t=aa in magic)
   apply (timeit \<open>shredder\<close>)
   by fastforce

lemma test_snd_idx0:
  "\<lbrakk>P (snd (x ! 0)); x \<noteq> []\<rbrakk> \<Longrightarrow> P (snd (x ! 0))"
  apply (erule thing)
   apply (cases x)
    apply fastforce
   apply (intro impI)
   apply clarsimp
   apply (erule_tac t=b in magic)
   apply (timeit \<open>shredder\<close>)
  apply fastforce
  done

lemma test_snd_idx1:
  "\<lbrakk>P (snd (xs ! 1)); length xs \<ge> 2\<rbrakk> \<Longrightarrow> P (snd (xs ! 1))"
  apply (erule thing)
   apply (case_tac xs, solves \<open>clarsimp\<close>)
   apply (rename_tac x0 xs')
   apply (case_tac xs', solves \<open>clarsimp\<close>)
   apply clarsimp
   apply (erule_tac t=ba in magic)
   apply (timeit \<open>shredder\<close>)
  apply fastforce
  done

lemma list_unmake:
  "\<lbrakk>length xs \<ge> n; n = Suc n'\<rbrakk> \<Longrightarrow> \<exists>x xs'. xs = x # xs' \<and> length xs' \<ge> n'"
  by (case_tac xs; fastforce)

method list_ripper = (rule list_unmake)

lemma list_fest:
  "\<lbrakk>P (xs ! 1 ! 2 ! 0 ! 1);
    length xs \<ge> 2;
    length (xs ! 1) \<ge> 3;
    length (xs ! 1 ! 2) \<ge> 1;
    length (xs ! 1 ! 2 ! 0) \<ge> 2\<rbrakk> \<Longrightarrow>
   P (xs ! 1 ! 2 ! 0 ! 1)"
  apply (erule thing)
  (* Split the list *)
  apply (drule_tac xs=xs in list_unmake, fastforce, clarsimp)
  apply (drule_tac xs=xs' in list_unmake, fastforce, clarsimp)
  apply (drule_tac xs=xa in list_unmake, fastforce, clarsimp)
  apply (drule_tac xs=xs' in list_unmake, fastforce, clarsimp)
  apply (drule_tac xs=xs'b in list_unmake, fastforce, clarsimp)
  apply (drule_tac xs=xc in list_unmake, fastforce, clarsimp)
  apply (drule_tac xs=xd in list_unmake, fastforce, clarsimp)
  apply (drule_tac xs=xs'c in list_unmake, fastforce, clarsimp)
thm subst
  apply (erule_tac t=xd in magic)
  apply (timeit \<open>shredder\<close>)
  by fastforce