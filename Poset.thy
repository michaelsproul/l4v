theory Poset
  imports Main
begin 

(* Datatype for partially ordered sets *)
datatype 'a poset = Poset (carrier: "'a set") (less: "'a \<Rightarrow> 'a \<Rightarrow> bool option")

(* Predicate that encodes the essential properties of a partially ordered set *)
definition partial_order :: "'a poset \<Rightarrow> bool" where
  "partial_order p \<equiv>
    \<comment> \<open>Well-formedness\<close>
    (\<forall>x y. less p x y \<noteq> None \<longrightarrow> (x \<in> carrier p \<and> y \<in> carrier p))
    \<comment> \<open>Reflexivity\<close>
    \<and> (\<forall>x \<in> carrier p. less p x x = Some True)
    \<comment> \<open>Antisymmetry\<close>
    \<and> (\<forall>x \<in> carrier p.
       \<forall>y \<in> carrier p.
         less p x y = Some True \<and> less p y x = Some True \<longrightarrow> x = y)
    \<comment> \<open>Transitivity\<close>
    \<and> (\<forall>x \<in> carrier p.
       \<forall>y \<in> carrier p.
       \<forall>z \<in> carrier p.
         less p x y = Some True \<and> less p y z = Some True \<longrightarrow>
         less p x z = Some True)"

(* Datatype for totally ordered sets *)
datatype 'a totalset = Totalset (total_carrier: "'a set") (total_less: "'a \<Rightarrow> 'a \<Rightarrow> bool")

definition to_poset :: "'a totalset \<Rightarrow> 'a poset" where
  "to_poset p \<equiv> Poset (total_carrier p) (\<lambda>x y. Some (total_less p x y))"

definition total_order :: "'a totalset \<Rightarrow> bool" where
  "total_order p \<equiv> partial_order (to_poset p)"

definition AND :: "'a poset \<Rightarrow> 'a poset \<Rightarrow> 'a poset"
  where
  "AND p1 p2 \<equiv> Poset (carrier p1 \<union> carrier p2)
                     (\<lambda>x y. if less p1 x y = Some True \<or> less p2 x y = Some True then Some True else None)"

lemma AND_correct:
  "\<lbrakk>partial_order p1; partial_order p2; carrier p1 \<inter> carrier p2 = {}\<rbrakk> \<Longrightarrow> partial_order (AND p1 p2)"
  (* FIXME: The simplifier seems to loop here on partial_order_def, not sure why yet *)
  apply (clarsimp simp: AND_def)
  apply (unfold partial_order_def)
  apply (intro conjI impI allI ballI)
  sorry

definition LIN :: "'a poset \<Rightarrow> 'a totalset" where
  "LIN p \<equiv> Totalset (carrier p) 
                    (* FIXME: handle the case where the existing comparison operator is not defined *)
                    (\<lambda>x y. if less p x y \<noteq> None then the (less p x y) else undefined)"

lemma LIN_correct:
  "\<lbrakk>partial_order p; p' = LIN p\<rbrakk> \<Longrightarrow>
    total_order p' \<and> (\<forall>x \<in> carrier p. \<forall>y \<in> carrier p. less p x y = Some True \<longrightarrow> total_less p' x y)"
  sorry

end