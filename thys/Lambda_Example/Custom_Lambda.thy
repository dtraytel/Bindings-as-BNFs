theory Custom_Lambda
  imports Datatype_TVsubst
begin

lemma vvsubst_arg_cong:
  fixes x y :: "'a :: var_TT TT"
  assumes f: "|supp f| <o bound(any::'a)" and g: "|supp g| <o bound(any::'a)" and "x = y"
     "(\<And>z. z \<in> FFVars x \<Longrightarrow> f z = g z)"
   shows "vvsubst f x = vvsubst g y"
  using assms by (auto intro!: vvsubst_cong)

lemma tvsubst_arg_cong:
  fixes x y :: "'a :: var_TT TT"
  assumes f: "|SSupp f| <o bound(any::'a)" and g: "|SSupp g| <o bound(any::'a)" and "x = y"
     "(\<And>z. z \<in> FFVars x \<Longrightarrow> f z = g z)"
   shows "tvsubst f x = tvsubst g y"
  using assms by (auto intro!: tvsubst_cong)

definition "Var a \<equiv> cctor (C1 a)"
definition "Lam a t \<equiv> cctor (C2 a t)"
definition "App t1 t2 \<equiv> cctor (C3 t1 t2)"

lemmas TT_ctr_defs = Var_def Lam_def App_def

(* Basic properties of the constructors: *)
lemma TT_FFVars_simps[simp]:
  "FFVars (Var a) = {a}"
  "FFVars (App t1 t2) = (FFVars t1 \<union> FFVars t2)"
  "FFVars (Lam a t) = (FFVars t - {a})"
  unfolding TT_ctr_defs FFVars_simps
  by auto

lemma user_TT_distinct[simp, induct_simp]:
  "Var a \<noteq> App s t"  "App s t \<noteq> Var a"
  "Var a \<noteq> Lam b t"  "Lam b t \<noteq> Var a"
  "App t1 t2 \<noteq> Lam a t" "Lam a t \<noteq> App t1 t2"
  by (auto simp: TT_ctr_defs TT_inject)

lemma user_TT_inject[simp, induct_simp]:
  fixes t1 t2 :: "'a::var_TT TT"
  shows
    "Var a = Var a' = (a = a')"
    "App t1 t2 = App t1' t2' = (t1 = t1' \<and> t2 = t2')"
  by (auto simp: TT_ctr_defs TT_inject supp_id_bound
    id_on_def intro!: exI[of _ id])

lemma Lam_same_injectE[elim_format]: "Lam a t = Lam a t' \<Longrightarrow> t = t'"
  apply (auto simp: TT_ctr_defs TT_inject supp_id_bound
    id_on_def intro!: trans[OF vvsubst_cong vvsubst_id, symmetric])
  done

lemma Lam_injectI:
"vusubst a a' t = t' \<Longrightarrow> a' \<notin> FFVars t \<Longrightarrow>
  Lam a t = Lam a' t'"
  apply (auto simp: TT_ctr_defs TT_inject vusubst_def
    supp_swap_bound bij_swap supp_id_upd id_on_def
      intro!: exI[of _ "id(a:=a',a':=a)"] vvsubst_cong)
  done

lemma Lam_diff_injectE[elim_format]:
  "Lam a t = Lam a' t' \<Longrightarrow> a \<noteq> a' \<Longrightarrow>
  (vusubst a a' t = t' \<and> a \<notin> FFVars t' \<and> a' \<notin> FFVars t)"
  apply (fastforce simp: TT_ctr_defs TT_inject vusubst_def
     FFVars_vvsubst
    supp_id_upd id_on_def intro!: exI[of _ "id(a:=a',a':=a)"]
      vvsubst_cong)
  done

lemma Lam_inject: "Lam a t = Lam a' t' =
  (if a = a' then t = t' else
    a \<notin> FFVars t' \<and> a' \<notin> FFVars t \<and> vusubst a a' t = t')"
  apply (rule iffI)
   apply (auto simp: FFVars_vusubst elim!: Lam_same_injectE
     elim: Lam_diff_injectE intro: Lam_injectI split: if_splits)
  done

lemma [simp,intro!]: "nnoclash x" by (cases x) (auto simp: nnoclash_def)

(* Simplification rules for variable-for-variables substitution: *)
(* The parallel version: *)
(* ... for arbitrary substitution functions, commutes with Lam
  only if the binding variable is avoided:  *)
lemma TT_vvsubst_simps[simp]:
  fixes f:: "'a \<Rightarrow> 'a::var_TT"
  assumes "|supp f| <o bound(any::'a::var_TT)"
  shows
    "vvsubst f (Var a) = Var (f a)"
    "vvsubst f (App t1 t2) = App (vvsubst f t1) (vvsubst f t2)"
    "a \<notin> imsupp f \<Longrightarrow> vvsubst f (Lam a t) = Lam a (vvsubst f t)"
  unfolding TT_ctr_defs by (subst vvsubst_cctor[OF assms]; auto)+

(* ... for bijective substitution functions, commutation with Lam
 holds unconditionally (and affects the binding variables too):  *)
lemma bij_TT_vvsubst_simps[simp]:
  fixes f:: "'a \<Rightarrow> 'a::var_TT"
  assumes "bij f" "|supp f| <o bound(any::'a::var_TT)"
  shows "vvsubst f (Lam a t) = Lam (f a) (vvsubst f t)"
  using assms by (auto simp: TT_ctr_defs  map_TT_cctor vvsubst_map_TT)

(* The unary version: *)
lemma TT_vusubst_simps[simp]:
    "vusubst a a' (Var b) = Var (if a = b then a' else b)"
    "vusubst a a' (App t1 t2) = App (vusubst a a' t1) (vusubst a a' t2)"
    "b \<noteq> a \<Longrightarrow> b \<noteq> a' \<Longrightarrow>
      vusubst a a' (Lam b t) = Lam b (vusubst a a' t)"
  unfolding TT_ctr_defs by (subst vusubst_cctor; auto)+

lemma VVr_Var[simp]: "VVr x = Var x"
  by (simp add: Var_def VVr_def \<eta>_def)

lemma TT_tvsubst_simps[simp]:
  fixes f:: "'a \<Rightarrow> 'a::var_TT TT"
  assumes "|SSupp f| <o bound(any::'a::var_TT)"
  shows
    "tvsubst f (Var a) = f a"
    "tvsubst f (App t1 t2) = App (tvsubst f t1) (tvsubst f t2)"
    "a \<notin> IImsupp f \<Longrightarrow> tvsubst f (Lam a t) = Lam a (tvsubst f t)"

  unfolding VVr_Var[symmetric] tvsubst_VVr[OF assms]
  unfolding TT_ctr_defs
  by (rule refl | subst tvsubst_cctor_not_isVVr[OF assms];
    auto simp: isVVr_def TT_ctr_defs TT_inject)+

lemma TT_tusubst_simps[simp]:
    "tusubst x z (Var y) = (if x = y then z else Var y)"
    "tusubst x z (App t1 t2) = App (tusubst x z t1) (tusubst x z t2)"
    "y \<noteq> x \<Longrightarrow> y \<notin> FFVars z \<Longrightarrow> tusubst x z (Lam y t) =
          Lam y (tusubst x z t)"
  unfolding VVr_Var[symmetric] tusubst_VVr
  unfolding TT_ctr_defs
  by (simp | subst tusubst_cctor_not_isVVr;
    auto simp: isVVr_def TT_ctr_defs TT_inject)+

(* Induction: *)
theorem user_TT_fresh_induct[case_names Var Lam App, consumes 1]:
  fixes T:: "'a::var_TT TT" and A :: "'a set"
  assumes bound: "|A| <o bound(any::'a::var_TT)"
      and var: "\<And>y. \<phi> (Var y)"
      and app: "\<And>t1 t2. \<phi> t1 \<Longrightarrow> \<phi> t2 \<Longrightarrow> \<phi> (App t1 t2)"
      and lam: "\<And>a t. \<phi> t \<Longrightarrow> (a \<notin> A \<Longrightarrow> \<phi> t) \<Longrightarrow> \<phi> (Lam a t)"
  shows "\<phi> t"
  using bound apply (induct t)
  subgoal for f
    by (cases f) (force simp: TT_ctr_defs[symmetric] intro!: var app lam)+
  done

theorem user_TT_finite_fresh_induct[case_names Var Lam App, consumes 1,
   induct type: TT]:
  fixes t:: "'a::var_TT TT" and A :: "'a set"
  assumes fin: "finite A"
      and var: "\<And>a. \<phi> (Var a)"
      and app: "\<And>t1 t2. \<phi> t1 \<Longrightarrow> \<phi> t2 \<Longrightarrow> \<phi> (App t1 t2)"
      and lam: "\<And>a t. a \<notin> A \<Longrightarrow> \<phi> t \<Longrightarrow> \<phi> (Lam a t)"
    shows "\<phi> T"
proof -
  from fin have "|A| <o bound(any::'a::var_TT)"
    by (intro ordLess_imp_ordLeq Cfinite_ordLess_Cinfinite)
      (auto simp: bound_cinfinite bound_Card_order cfinite_def)
  then show ?thesis
  apply (induct T)
  subgoal for f
    by (cases f) (force simp: TT_ctr_defs[symmetric] intro!: var app lam)+
  done
qed

(* Cardinality: *)
lemma finite_less_bound: "finite A \<Longrightarrow> |A| <o bound(any::'a::var_TT)"
  by (simp add: var_TT_infinite)

(* The above can be used to replace everywhere
the smallness assumption with the finiteness assumption,
for example: *)

thm user_TT_fresh_induct[OF finite_less_bound]
    TT_tvsubst_simps(3)[OF finite_less_bound,simp]

hide_type (open) F

(* Not covered here: The recursor will also be instantiated to the
concrete syntax, and customized for the concrete constructors.
*)


end