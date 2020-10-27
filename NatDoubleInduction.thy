theory NatDoubleInduction imports Main begin

hide_const Suc
datatype nat = Zero | Suc nat


text "Example exlpains a proof for a cutom induction rule"
lemma nat_induct: "\<lbrakk> P Zero; \<And>n. P n \<Longrightarrow> P (Suc n) \<rbrakk> \<Longrightarrow> P n"
  apply(rule nat.induct)
  apply(assumption)
  apply(assumption)
  done


text "Lemma to proof the double induction rule"
lemma nat_induct_N_0: "\<lbrakk> P Zero Zero; \<And>m n. P m n \<Longrightarrow> P (Suc m) n; \<And>m n. P m n \<Longrightarrow> P m (Suc n) \<rbrakk> \<Longrightarrow> P m Zero"
  apply(erule_tac n=m in nat_induct)
  apply(assumption)
  done


text "Double induction rule for \<nat> \<times> \<nat>"
theorem nat_induct_M_N: "\<lbrakk> P Zero Zero; \<And>m n. P m n \<Longrightarrow> P (Suc m) n; \<And>m n. P m n \<Longrightarrow> P m (Suc n) \<rbrakk> \<Longrightarrow> P m n"
  apply(rule nat_induct)
  apply(erule nat_induct_N_0)
  apply(assumption)
  apply(assumption)
  apply(assumption)
  done


fun nat_eq :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "nat_eq Zero Zero = True" |
  "nat_eq (Suc n) Zero = False" |
  "nat_eq Zero (Suc m) = False" |
  "nat_eq (Suc n) (Suc m) = nat_eq n m"


text "Example using the induction rule that implemented by me"
lemma nat_eq_refl: "nat_eq n n"
  apply(rule nat_induct)
  apply(subst nat_eq.simps)
  apply(rule TrueI)
  apply(subst nat_eq.simps)
  apply(assumption)
  done


(* TODO: Example using nat_induct_M_N *)

end