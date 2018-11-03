theory Custom_POPLmark1B
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

definition "TVar x \<equiv> cctor (FVar x)"
definition "TTop \<equiv> cctor FTop"
definition "TArr T U \<equiv> cctor (FArr T U)"
definition "TAll x T U \<equiv> cctor (FAll x T U)"
definition "TRec X \<equiv> cctor (FRec X)"

lemmas TT_ctr_defs = TVar_def TTop_def TArr_def TAll_def TRec_def

lemma TT_FFVars_simps[simp]:
  "FFVars (TVar y) = {y}"
  "FFVars TTop = {}"
  "FFVars (TArr T U) = (FFVars T \<union> FFVars U)"
  "FFVars (TAll y T U) = (FFVars T \<union> (FFVars U - {y}))"
  "FFVars (TRec X) = (\<Union>T \<in> values X. FFVars T)"
  unfolding TT_ctr_defs FFVars_simps
  by auto

theorem user_TT_fresh_induct[case_names TVar TTop TArr TAll TRec, consumes 1]:
  fixes T:: "'a::var_TT TT" and A :: "'a set"
  assumes bound: "|A| <o bound(any::'a::var_TT)"
      and tvar: "\<And>y. \<phi> (TVar y)"
      and ttop: "\<phi> TTop"
      and tarrow: "\<And>T U. \<phi> T \<Longrightarrow> \<phi> U \<Longrightarrow> \<phi> (TArr T U)"
      and tall: "\<And>y T U. \<phi> T \<Longrightarrow> (y \<notin> A \<Longrightarrow> \<phi> U) \<Longrightarrow> \<phi> (TAll y T U)"
      and trec: "\<And>X. (\<forall>T\<in>values X. \<phi> T) \<Longrightarrow> \<phi> (TRec X)"
  shows "\<phi> T"
  using bound apply (induct T)
  subgoal for f
    by (cases f) (force simp: TT_ctr_defs[symmetric] intro!: tvar ttop tarrow tall trec)+
  done

theorem user_TT_finite_fresh_induct[case_names TVar TTop TArr TAll TRec, consumes 1, induct type: TT]:
  fixes T:: "'a::var_TT TT" and A :: "'a set"
  assumes fin: "finite A"
      and tvar: "\<And>y. \<phi> (TVar y)"
      and ttop: "\<phi> TTop"
      and tarrow: "\<And>T U. \<phi> T \<Longrightarrow> \<phi> U \<Longrightarrow> \<phi> (TArr T U)"
      and tall: "\<And>y T U. y \<notin> A \<Longrightarrow> \<phi> T \<Longrightarrow> \<phi> U \<Longrightarrow> \<phi> (TAll y T U)"
      and trec: "\<And>X. (\<forall>T\<in>values X. \<phi> T) \<Longrightarrow> \<phi> (TRec X)"
    shows "\<phi> T"
proof -
  from fin have "|A| <o bound(any::'a::var_TT)"
    by (intro ordLess_imp_ordLeq Cfinite_ordLess_Cinfinite)
      (auto simp: bound_cinfinite bound_Card_order cfinite_def)
  then show ?thesis
  apply (induct T)
  subgoal for f
    by (cases f) (force simp: TT_ctr_defs[symmetric] intro!: tvar ttop tarrow tall trec)+
  done
qed

lemma user_TT_distinct[simp, induct_simp]:
  "TVar y \<noteq> TTop"
  "TVar y \<noteq> TArr T U"
  "TVar y \<noteq> TAll x S V"
  "TVar y \<noteq> TRec X"
  "TTop \<noteq> TVar y"
  "TTop \<noteq> TArr T U"
  "TTop \<noteq> TAll x S V"
  "TTop \<noteq> TRec X"
  "TArr T U \<noteq> TVar y"
  "TArr T U \<noteq> TTop"
  "TArr T U \<noteq> TAll x S V"
  "TArr T U \<noteq> TRec X"
  "TAll x S V \<noteq> TVar y"
  "TAll x S V \<noteq> TTop"
  "TAll x S V \<noteq> TArr T U"
  "TAll x S V \<noteq> TRec X"
  "TRec X \<noteq> TVar y"
  "TRec X \<noteq> TTop"
  "TRec X \<noteq> TArr T U"
  "TRec X \<noteq> TAll x S V"
  by (auto simp: TT_ctr_defs TT_inject)

lemma user_TT_inject[simp, induct_simp]:
  fixes T :: "'a::var_TT TT" and X :: "(nat, 'a::var_TT TT) lfset"
  shows
    "TVar x = TVar x' = (x = x')"
    "TArr T U = TArr T' U' = (T = T' \<and> U = U')"
    "TRec X = TRec X' = (X = X')"
  by (auto simp: TT_ctr_defs TT_inject lfset.map_id supp_id_bound
    id_on_def lfset.map_id[unfolded map_lfset_id_def] intro!: exI[of _ id])

lemma TAll_same_injectE[elim_format]: "TAll x T U = TAll x T' U' \<Longrightarrow>
  (T = T' \<and> U = U')"
  apply (auto simp: TT_ctr_defs TT_inject supp_id_bound
    id_on_def intro!: trans[OF vvsubst_cong vvsubst_id, symmetric])
  done

lemma TAll_diff_injectE[elim_format]: "TAll x T U = TAll y T' U' \<Longrightarrow> x \<noteq> y \<Longrightarrow>
  (T = T' \<and> vusubst x y U = U' \<and> x \<notin> FFVars U' \<and> y \<notin> FFVars U)"
  apply (fastforce simp: TT_ctr_defs TT_inject vusubst_def FFVars_vvsubst
    supp_id_upd id_on_def intro!: exI[of _ "id(x:=y,y:=x)"] vvsubst_cong)
  done

lemma TAll_injectI: "T = T' \<Longrightarrow> vusubst x y U = U' \<Longrightarrow> y \<notin> FFVars U \<Longrightarrow>
  TAll x T U = TAll y T' U'"
  apply (auto simp: TT_ctr_defs TT_inject vusubst_def
    supp_swap_bound bij_swap supp_id_upd id_on_def intro!: exI[of _ "id(x:=y,y:=x)"] vvsubst_cong)
  done


lemma TAll_inject: "TAll x T U = TAll y T' U' =
  (T = T' \<and> (if x = y then U = U' else
    x \<notin> FFVars U' \<and> y \<notin> FFVars U \<and> vusubst x y U = U'))"
  apply (rule iffI)
   apply (auto simp: FFVars_vusubst elim!: TAll_same_injectE
     elim: TAll_diff_injectE intro: TAll_injectI split: if_splits)
  done

theorem user_TT_plain_induct[case_names TVar TTop TArr TAll TRec]:
  fixes T:: "'a::var_TT TT"
  assumes tvar: "\<And>y. \<phi> (TVar y)"
      and ttop: "\<phi> TTop"
      and tarrow: "\<And>T U. \<phi> T \<Longrightarrow> \<phi> U \<Longrightarrow> \<phi> (TArr T U)"
      and tall: "\<And>y T U. \<phi> T \<Longrightarrow> \<phi> U \<Longrightarrow> \<phi> (TAll y T U)"
      and trec: "\<And>X. (\<forall>T\<in>values X. \<phi> T) \<Longrightarrow> \<phi> (TRec X)"
  shows "\<phi> T"
  apply (induct T rule: TT_plain_induct)
  subgoal for f
    by (cases f) (force simp: TT_ctr_defs[symmetric] intro!: tvar ttop tarrow tall trec)+
  done

theorem user_TT_fresh_induct_param[case_names TVar TTop TArr TAll TRec, consumes 1]:
  fixes t:: "'a::var_TT TT"
  and Param :: "'param set" and varsOf :: "'param \<Rightarrow> 'a set"
  assumes param: "\<forall>\<rho> \<in> Param. |varsOf \<rho>| <o bound(any::'a::var_TT)"
      and tvar: "\<And>y \<rho>. \<phi> (TVar y) \<rho>"
      and ttop: "\<And>\<rho>. \<phi> TTop \<rho>"
      and tarrow: "\<And>T U \<rho>. (\<And>\<rho>. \<rho> \<in> Param \<Longrightarrow> \<phi> T \<rho>) \<Longrightarrow> (\<And>\<rho>. \<rho> \<in> Param \<Longrightarrow> \<phi> U \<rho>) \<Longrightarrow> \<phi> (TArr T U) \<rho>"
      and tall: "\<And>y T U \<rho>. y \<notin> varsOf \<rho> \<Longrightarrow>  (\<And>\<rho>. \<rho> \<in> Param \<Longrightarrow> \<phi> T \<rho>) \<Longrightarrow> (\<And>\<rho>. \<rho> \<in> Param \<Longrightarrow> \<phi> U \<rho>) \<Longrightarrow> \<phi> (TAll y T U) \<rho>"
      and trec: "\<And>X \<rho>. (\<And>\<rho>. \<rho> \<in> Param \<Longrightarrow> \<forall>T\<in>values X. \<phi> T \<rho>) \<Longrightarrow> \<phi> (TRec X) \<rho>"
    shows "\<forall> \<rho> \<in> Param. \<phi> T \<rho>"
  using param[rule_format] apply (induct T rule: TT_fresh_induct_param)
   apply assumption
  subgoal for f
    by (cases f) (force simp: TT_ctr_defs[symmetric] intro!: tvar ttop tarrow tall trec)+
  done

theorem user_TT_fresh_induct_param_UNIV[case_names TVar TTop TArr TAll TRec, consumes 1]:
  fixes t:: "'a::var_TT TT" and varsOf :: "'param \<Rightarrow> 'a set"
  assumes param: "\<forall>\<rho>. |varsOf \<rho>| <o bound(any::'a::var_TT)"
      and tvar: "\<And>y \<rho>. \<phi> (TVar y) \<rho>"
      and ttop: "\<And>\<rho>. \<phi> TTop \<rho>"
      and tarrow: "\<And>T U \<rho>. (\<And>\<rho>. \<phi> T \<rho>) \<Longrightarrow> (\<And>\<rho>. \<phi> U \<rho>) \<Longrightarrow> \<phi> (TArr T U) \<rho>"
      and tall: "\<And>y T U \<rho>. y \<notin> varsOf \<rho> \<Longrightarrow>  (\<And>\<rho>. \<phi> T \<rho>) \<Longrightarrow> (\<And>\<rho>. \<phi> U \<rho>) \<Longrightarrow> \<phi> (TAll y T U) \<rho>"
      and trec: "\<And>X \<rho>. (\<And>\<rho>.  \<forall>T\<in>values X. \<phi> T \<rho>) \<Longrightarrow> \<phi> (TRec X) \<rho>"
    shows "\<forall> \<rho>. \<phi> T \<rho>"
  by (rule user_TT_fresh_induct_param[of UNIV varsOf \<phi> T, unfolded ball_UNIV]) (auto intro!: assms)

lemma TT_vvsubst_simps[simp]:
  fixes f:: "'a \<Rightarrow> 'a::var_TT"
  assumes "|supp f| <o bound(any::'a::var_TT)"
  shows
    "vvsubst f (TVar y) = TVar (f y)"
    "vvsubst f TTop = TTop"
    "vvsubst f (TArr T U) = TArr (vvsubst f T) (vvsubst f U)"
    "y \<notin> imsupp f \<Longrightarrow> y \<notin> FFVars T \<Longrightarrow> vvsubst f (TAll y T U) = TAll y (vvsubst f T) (vvsubst f U)"
    "vvsubst f (TRec X) = TRec (map_lfset_id (vvsubst f) X)"
  unfolding TT_ctr_defs by (subst vvsubst_cctor[OF assms]; auto simp: nnoclash_def)+

lemma bij_TT_vvsubst_simps[simp]:
  fixes f:: "'a \<Rightarrow> 'a::var_TT"
  assumes "bij f" "|supp f| <o bound(any::'a::var_TT)"
  shows "vvsubst f (TAll y T U) = TAll (f y) (vvsubst f T) (vvsubst f U)"
  unfolding TT_ctr_defs unfolding vvsubst_map_TT[OF assms]
  by (subst map_TT_cctor[OF assms]; auto)+

lemma TT_vusubst_simps[simp]:
    "vusubst x z (TVar y) = TVar (if x = y then z else y)"
    "vusubst x z TTop = TTop"
    "vusubst x z (TArr T U) = TArr (vusubst x z T) (vusubst x z U)"
    "y \<noteq> x \<Longrightarrow> y \<noteq> z \<Longrightarrow> y \<notin> FFVars T \<Longrightarrow> vusubst x z (TAll y T U) = TAll y (vusubst x z T) (vusubst x z U)"
    "vusubst x z (TRec X) = TRec (map_lfset_id (vusubst x z) X)"
  unfolding TT_ctr_defs by (subst vusubst_cctor; auto simp: nnoclash_def)+

lemma VVr_TVar[simp]: "VVr x = TVar x"
  by (simp add: TVar_def VVr_def \<eta>_def)

lemma TT_tvsubst_simps[simp]:
  fixes f:: "'a \<Rightarrow> 'a::var_TT TT"
  assumes "|SSupp f| <o bound(any::'a::var_TT)"
  shows
    "tvsubst f (TVar y) = f y"
    "tvsubst f TTop = TTop"
    "tvsubst f (TArr T U) = TArr (tvsubst f T) (tvsubst f U)"
    "y \<notin> IImsupp f \<Longrightarrow> y \<notin> FFVars T \<Longrightarrow> tvsubst f (TAll y T U) = TAll y (tvsubst f T) (tvsubst f U)"
    "tvsubst f (TRec X) = TRec (map_lfset_id (tvsubst f) X)"
  unfolding VVr_TVar[symmetric] tvsubst_VVr[OF assms]
  unfolding TT_ctr_defs
  by (rule refl | subst tvsubst_cctor_not_isVVr[OF assms];
    auto simp: isVVr_def TT_ctr_defs TT_inject nnoclash_def)+

lemma TT_tusubst_simps[simp]:
    "tusubst x z (TVar y) = (if x = y then z else TVar y)"
    "tusubst x z TTop = TTop"
    "tusubst x z (TArr T U) = TArr (tusubst x z T) (tusubst x z U)"
    "y \<noteq> x \<Longrightarrow> y \<notin> FFVars z \<Longrightarrow>y \<notin> FFVars T \<Longrightarrow>  tusubst x z (TAll y T U) = TAll y (tusubst x z T) (tusubst x z U)"
    "tusubst x z (TRec X) = TRec (map_lfset_id (tusubst x z) X)"
  unfolding VVr_TVar[symmetric] tusubst_VVr
  unfolding TT_ctr_defs
  by (simp | subst tusubst_cctor_not_isVVr;
    auto simp: isVVr_def TT_ctr_defs TT_inject nnoclash_def)+

lemma finite_less_bound: "finite A \<Longrightarrow> |A| <o bound(any::'a::var_TT)"
  by (simp add: var_TT_infinite)

lemma finite_FFVars: "finite (FFVars t)"
  by (induct t rule: user_TT_plain_induct) auto

lemma bij_vvsubst:
  fixes f :: "'a :: var_TT \<Rightarrow> 'a"
  shows "bij f \<Longrightarrow> |supp f| <o bound(any :: 'a) \<Longrightarrow> bij (vvsubst f)"
  apply (rule o_bij[of "vvsubst (inv f)"])
   apply (rule ext, rule trans[OF o_apply], rule trans[OF vvsubst_o[symmetric]];
     simp only: supp_inv_bound inv_o_simp1 vvsubst_id id_apply)
   apply (rule ext, rule trans[OF o_apply], rule trans[OF vvsubst_o[symmetric]];
     simp only: supp_inv_bound inv_o_simp2 vvsubst_id id_apply)
  done

lemma rel_TT_compp: fixes u v :: "'a :: var_TT \<Rightarrow> 'a"
  shows "|supp u| <o bound(any :: 'a) \<Longrightarrow> |supp v| <o bound(any :: 'a) \<Longrightarrow>
    rel_TT (u o v) = rel_TT v OO rel_TT u"
  by (auto simp: fun_eq_iff rel_TT_def relcompp_apply Grp_def vvsubst_o)

theorem vvsubst_id0: "vvsubst id = id"
  unfolding vvsubst_id fun_eq_iff id_apply by simp

hide_type (open) F

end