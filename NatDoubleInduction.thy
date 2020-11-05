theory NatDoubleInduction imports Main begin

hide_const Suc
datatype nat = Zero | Suc nat


section "How to define custom induction rules"
subsection "Example for cutom induction rules"
lemma nat_induct: "\<lbrakk> P Zero; \<And>n. P n \<Longrightarrow> P (Suc n) \<rbrakk> \<Longrightarrow> P n"
  apply(rule nat.induct)
  apply(assumption)
  apply(assumption)
  done


fun nat_eq :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  nat_eq_ZeroZero: "nat_eq Zero Zero = True" |
  nat_eq_SucZero:  "nat_eq (Suc n) Zero = False" |
  nat_eq_ZeroSuc:  "nat_eq Zero (Suc m) = False" |
  nat_eq_SucSuc:   "nat_eq (Suc n) (Suc m) = nat_eq n m"


text "Single-induction example using the custom induction rule"
lemma nat_eq_refl: "nat_eq n n"
  apply(rule nat_induct)
  apply(subst nat_eq_ZeroZero)
  apply(rule TrueI)
  apply(subst nat_eq_SucSuc)
  apply(assumption)
  done


lemma nat_eq_sym[rule_format]: "\<forall>n. nat_eq m n \<longleftrightarrow> nat_eq n m"
  apply(rule nat_induct)
  apply(rule allI)
  apply(rule_tac y=n in nat.exhaust)
  apply(erule ssubst)
  apply(subst (1 2) nat_eq_ZeroZero)
  apply(rule refl)
  apply(erule ssubst)
  apply(subst nat_eq_SucZero)
  apply(subst nat_eq_ZeroSuc)
  apply(rule refl)
  apply(rule allI)
  apply(rule_tac y=na in nat.exhaust)
  apply(erule ssubst)
  apply(subst nat_eq_SucZero)
  apply(subst nat_eq_ZeroSuc)
  apply(rule refl)
  apply(erule ssubst)
  apply(subst (1 2) nat_eq_SucSuc)
  apply(drule_tac x=x2 in spec)
  apply(assumption)
  done


fun nat_plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  nat_plus_ZeroFree: "nat_plus Zero n = n" |
  nat_plus_SucFree:  "nat_plus (Suc m) n = nat_plus m (Suc n)"


lemma nat_plus_FreeSuc[rule_format]: "\<forall>n. nat_plus m (Suc n) = Suc (nat_plus m n)"
  apply(rule_tac n=m in nat_induct)
  apply(subst (1 2) nat_plus_ZeroFree)
  apply(rule allI)
  apply(rule refl)

  apply(simp only: nat_plus_SucFree)
  apply(rule allI)
  apply(subst nat.simps(1))
  apply(subst nat.simps(1))
  apply(rule refl)
  done


subsection "Double-induction example using the custom induction rule"
lemma "nat_eq (nat_plus m n) (nat_plus n m)"
  apply(rule_tac n=m in nat_induct)
  apply(rule_tac n=n in nat_induct)
  apply(unfold nat_plus_ZeroFree nat_eq_ZeroZero)
  apply(rule TrueI)

  apply(rule_tac y=n in nat.exhaust)
  apply(clarify)
  apply(unfold nat_plus_SucFree nat_plus_ZeroFree nat_eq_SucSuc nat_eq_ZeroZero)
  apply(rule TrueI)

  apply(clarify)
  apply(unfold nat_plus_SucFree nat_plus_ZeroFree nat_plus_FreeSuc nat_eq_SucSuc)
  apply(assumption)
  apply(assumption)
  done


section "How to define double-induction rules"
subsection "Lemmas to proof the double induction rule"
lemma nat_induct_N_M: "\<lbrakk> P Zero Zero; \<And>m n. P m n \<Longrightarrow> P (Suc m) n; \<And>m n. P m n \<Longrightarrow> P m (Suc n) \<rbrakk> \<Longrightarrow> P m n"
  apply(rule_tac n=m in nat_induct)
  apply(rule_tac n=n in nat_induct)
  apply(assumption)

  apply(drule_tac P="\<lambda>m. (\<And>n. P m n \<Longrightarrow> P m (Suc n))"  and x="Zero" in meta_spec)
  apply(drule_tac P="\<lambda>n. (P Zero n \<Longrightarrow> P Zero (Suc n))"  and x="n" in meta_spec)
  apply(drule meta_mp)
  apply(assumption)
  apply(assumption)

  apply(drule_tac P="\<lambda>m. (\<And>n. P m n \<Longrightarrow> P (Suc m) n)" and x="na" in meta_spec)
  apply(drule_tac P="\<lambda>n. (P na n \<Longrightarrow> P (Suc na) n)" and x="n" in meta_spec)
  apply(drule meta_mp)
  apply(assumption)
  apply(assumption)
  done


subsection "Proof using the custom double-induction rule"
lemma "nat_eq (nat_plus m n) (nat_plus n m)"
  apply(rule_tac n=n and m=m in nat_induct_N_M)
  apply(unfold nat_plus_ZeroFree)
  apply(subst nat_eq_ZeroZero)
  apply(rule TrueI)
  apply(unfold nat_plus_SucFree nat_plus_FreeSuc nat_eq_SucSuc)
  apply(assumption)
  apply(assumption)
  done
end