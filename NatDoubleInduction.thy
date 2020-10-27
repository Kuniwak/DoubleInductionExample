theory NatDoubleInduction imports Main begin

hide_const Suc
datatype nat = Zero | Suc nat


text "Example for proof like induction rules"
lemma "P Zero \<and> (\<forall>n. P n \<longrightarrow> P (Suc n)) \<longrightarrow> P n"
  apply(rule nat.induct)
  apply(rule impI)
  apply(erule conjE)
  apply(assumption)

  apply(rule impI)
  apply(drule mp)
  apply(assumption)
  apply(erule conjE)
  apply(drule_tac x=x in spec)
  apply(drule mp)
  apply(assumption)
  apply(assumption)
  done


text "Lemma to proof the double induction rule"
lemma nat_induct_N_0[rule_format]: "P Zero Zero \<and> (\<forall>m n. P m n \<longrightarrow> P (Suc m) n) \<and> (\<forall>m n. P m n \<longrightarrow> P m (Suc n)) \<longrightarrow> P m Zero"
  apply(rule_tac nat=m in nat.induct)
  apply(rule impI)
  apply(elim conjE)
  apply(assumption)

  apply(rule impI)
  apply(drule mp)
  apply(assumption)

  apply(elim conjE)
  apply(drule_tac x=x and P="\<lambda>m. \<forall>n. P m n \<longrightarrow> P (Suc m) n" in spec)
  apply(drule_tac x=Zero and P="\<lambda>n. P x n \<longrightarrow> P (Suc x) n" in spec)
  apply(drule mp)
  apply(assumption)
  apply(assumption)
  done


text "Double induction rule for \<real> \<times> \<real>"
theorem nat_induct_M_N[rule_format]: "P Zero Zero \<and> (\<forall>m n. P m n \<longrightarrow> P (Suc m) n) \<and> (\<forall>m n. P m n \<longrightarrow> P m (Suc n)) \<longrightarrow> (P m n)"
  apply(rule nat.induct)
  apply(rule impI)
  apply(elim conjE)

  apply(rule nat_induct_N_0)
  apply(erule conjI)
  apply(erule conjI)
  apply(assumption)

  apply(intro impI)
  apply(elim conjE)

  apply(drule mp)
  apply(erule conjI)
  apply(erule conjI)
  apply(assumption)

  apply(drule_tac x=m and P="\<lambda>m. \<forall>n. P m n \<longrightarrow> P m (Suc n)" in spec)
  apply(drule_tac x=x and P="\<lambda>n. P m n \<longrightarrow> P m (Suc n)" in spec)
  apply(drule mp)
  apply(assumption)
  apply(assumption)
  done


fun nat_eq :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nat_eq Zero Zero = True" |
  "nat_eq (Suc n) Zero = False" |
  "nat_eq Zero (Suc m) = False" |
  "nat_eq (Suc n) (Suc m) = nat_eq n m"


lemma nat_eq_refl: "nat_eq n n"
  apply(rule nat.induct)
  apply(subst nat_eq.simps)
  apply(rule TrueI)
  apply(subst nat_eq.simps)
  apply(assumption)
  done

(* TODO: Example using nat_induct_M_N *)

end