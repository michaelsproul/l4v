theory Test
imports
  "HOL.HOL"
  "Lib.Lib"
begin

lemma indentation_depth_test:
  "P \<and> Q \<Longrightarrow> P"
  using [[goals_limit = 1000]]
  apply (subgoal_tac "Q")
   apply (subgoal_tac "Q")
    apply (subgoal_tac "Q")
     apply (subgoal_tac "Q")
      apply (subgoal_tac "Q")
       apply (subgoal_tac "Q")
        apply (subgoal_tac "Q")
         apply (subgoal_tac "Q")
          apply (subgoal_tac "Q")
           apply (subgoal_tac "Q")
            apply (subgoal_tac "Q")
             apply (subgoal_tac "Q")
              apply (subgoal_tac "Q")
               apply (subgoal_tac "Q")
                apply (subgoal_tac "Q")
                 apply (subgoal_tac "Q")
                  apply (subgoal_tac "Q")
                   apply (subgoal_tac "Q")
                    apply (subgoal_tac "Q")
                     apply (subgoal_tac "Q")
                      apply (subgoal_tac "Q")
                       apply (subgoal_tac "Q")
                        apply (subgoal_tac "Q")
                         apply (subgoal_tac "Q")
                          apply (subgoal_tac "Q")
                           apply (subgoal_tac "Q")
                            apply (subgoal_tac "Q")
                             apply (subgoal_tac "Q")
                              apply (subgoal_tac "Q")
                               apply (subgoal_tac "Q")
                                apply (subgoal_tac "Q")
                                 apply (subgoal_tac "Q")
                                  apply (subgoal_tac "Q")
                                   apply (subgoal_tac "Q")
                                    apply (subgoal_tac "Q")
                                     apply (subgoal_tac "Q")
                                      apply (subgoal_tac "Q")
                                       apply (subgoal_tac "Q")
                                        apply (subgoal_tac "Q")
                                         apply (subgoal_tac "Q")
                                          apply (subgoal_tac "Q")
                                           apply (subgoal_tac "Q")
                                            apply (subgoal_tac "Q")
                                             apply (subgoal_tac "Q")
                                              apply (subgoal_tac "Q")
                                               apply (subgoal_tac "Q")
                                                apply (subgoal_tac "Q")
                                                 apply (subgoal_tac "Q")
                                                  apply (subgoal_tac "Q")
                                                   apply (subgoal_tac "Q")
                                                    apply (subgoal_tac "Q")
                                                     apply (subgoal_tac "Q")
                                                      apply (subgoal_tac "Q")
                                                       apply (subgoal_tac "Q")
                                                        apply (subgoal_tac "Q")
                                                         apply (subgoal_tac "Q")
                                                          apply (subgoal_tac "Q")
                                                           apply (subgoal_tac "Q")
                                                            apply (subgoal_tac "Q")
                                                             apply (subgoal_tac "Q")
                                                              apply (subgoal_tac "Q")
                                                               apply (subgoal_tac "Q")
                                                                apply (subgoal_tac "Q")
                                                                 apply (subgoal_tac "Q")
                                                                  apply (subgoal_tac "Q")
                                                                   apply simp
                                                                  apply simp
                                                                 apply simp
                                                                apply simp
                                                               apply simp
                                                              apply simp
                                                             apply simp
                                                            apply simp
                                                           apply simp
                                                          apply simp
                                                         apply simp
                                                        apply simp
                                                       apply simp
                                                      apply simp
                                                     apply simp
                                                    apply simp
                                                   apply simp
                                                  apply simp
                                                 apply simp
                                                apply simp
                                               apply simp
                                              apply simp
                                             apply simp
                                            apply simp
                                           apply simp
                                          apply simp
                                         apply simp
                                        apply simp
                                       apply simp
                                      apply simp
                                     apply simp
                                    apply simp
                                   apply simp
                                  apply simp
                                 apply simp
                                apply simp
                               apply simp
                              apply simp
                             apply simp
                            apply simp
                           apply simp
                          apply simp
                         apply simp
                        apply simp
                       apply simp
                      apply simp
                     apply simp
                    apply simp
                   apply simp
                  apply simp
                 apply simp
                apply simp
               apply simp
              apply simp
             apply simp
            apply simp
           apply simp
          apply simp
         apply simp
        apply simp
       apply simp
      apply simp
     apply simp
    apply simp
   apply simp
  apply simp
  done

definition thing1 ::
  "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "thing1 x y = x * 5 + x ^ y"

definition thing2 ::
  "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "thing2 x y = x * 5"

definition thing3 ::
  "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "thing3 x y = x ^ y"

lemma attribute_test_easy:
  "thing1 x y = thing2 x y + thing3 x y"
  apply (clarsimp simp: Collect_const
                  simp: thing1_def
                  simp: thing2_def thing3_def)
  done

lemma attribute_test_multi:
  "thing1 x y = thing2 x y + thing3 x y"
  apply (clarsimp simp del: Collect_const
                      simp: thing1_def
                      simp: thing2_def
                            thing3_def
                     intro: conjI
                      dest: disjE)
  done

lemma attribute_test_lots_of_rules:
  "thing1 x y = thing2 x y + thing3 x y"
  apply (clarsimp intro: disjI1 disjI1
                  simp: thing1_def thing2_def
                        conjI
                        disjE
                  simp: thing3_def)
  done

lemma bad_alternative1:
  "thing1 x y = thing2 x y + thing3 x y"
  apply (simp add: thing1_def |
         clarsimp simp: thing2_def |
         fastforce simp add: thing3_def)+
  done

lemma bad_alternative2:
  "thing1 x y = thing2 x y + thing3 x y"
  apply (simp add: thing1_def |
         fastforce |
         fastforce simp: thing3_def |
         clarsimp simp: thing2_def)+
  done

lemma inner_syntax_wrap:
  "thing1 x y = thing2 x y + thing3 x y"
  apply (insert bad_alternative2
                 [where x="if True
                           then x
                           else x"])
  by clarsimp

lemma lname:
  "\<lbrakk> P x ; P x \<Longrightarrow> Q x \<rbrakk>
   \<Longrightarrow> Q x"
proof -
  fix x
  obtain y where "y
       = x"
  and "y
= x"
    sorry
qed

lemma lname:
  "\<lbrakk> P x ; P x \<Longrightarrow> Q x \<rbrakk>
   \<Longrightarrow> Q x"
proof -

(* Future work: making subgoal great again *)
lemma subgoal_magic:
  "thing1 x y + thing2 x y = 2 * (thing2 x y) + thing3 x y"
  apply (subgoal_tac "thing1 x y = thing2 x y + thing3 x y")
   apply (subgoal_tac "thing1 x y = thing2 x y + thing3 x y")
    apply (subgoal_tac "thing1 x y = thing2 x y + thing3 x y")
     apply (subgoal_tac "thing1 x y = thing2 x y + thing3 x y")
  subgoal
    apply (clarsimp simp: attribute_test_multi)
    done
     apply (simp add: attribute_test_multi)+
  done

(* Future work: where/rule_tac variable instantiations *)
lemma rule_with_lots_of_vars:
  "x + y + z + longer_var + really_long_var_name = awesomely_long_var_name"
  sorry

lemma where_test_easy:
  "5 + 8 + 9 + (1023 * 5) + 1823213 = 0"
  apply (rule rule_with_lots_of_vars[where x=5 and
      y=8 and
      z=9 and
      longer_var="1023 * 5" and
      really_long_var_name="1823213" and
      awesomely_long_var_name="0"])
  done

lemma rule_tac_test_easy:
  "5 + 8 + 9 + (1023 * 5) + 1823213 = 0"
  apply (rule_tac x=5 and
    y=8 and
    z=9 and
    longer_var="1023 * 5" and
    really_long_var_name="1823213" and
    awesomely_long_var_name="0" in
    rule_with_lots_of_vars)
  done

end
