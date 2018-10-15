theory Datatype_VVsubst
imports Datatype_Recursion_Template
begin


typedef 'a :: var_TT ssfun = "{f :: 'a \<Rightarrow> 'a. |supp f| <o bound(any :: 'a)}"
  by (auto intro!: exI[of _ id] simp: supp_id_bound)

setup_lifting type_definition_ssfun

lift_definition idSS :: "'a :: var_TT ssfun" is id
  by (simp add: supp_id_bound)

context
  fixes u :: "'a :: var_TT \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o bound(any :: 'a)"
begin

lift_definition compSS :: "'a :: var_TT ssfun \<Rightarrow> 'a ssfun" is "\<lambda>p. u o p o inv u"
  by (simp add: supp_comp_bound supp_inv_bound u)

end

context
  fixes u :: "'a :: var_TT \<Rightarrow> 'a"
  assumes u[transfer_rule, simp]: "bij u" "|supp u| <o bound(any :: 'a)"
begin

lemma compSS_inv_compSS[simp]: "compSS (inv u) (compSS u p) = p"
  supply bij_imp_bij_inv[transfer_rule] supp_inv_bound[transfer_rule]
  apply transfer
  apply auto
  done

end

lemma compSS_id[simp]: "compSS id = id"
  supply supp_id_bound[transfer_rule] bij_id[transfer_rule] by (rule ext, transfer) auto

template_instance VVSUBST: REC where
  'a REC.P = "'a ssfun" and 'a REC.C = "'a TT"
for
  "REC.A :: 'a::var_TT set"
  = "{} :: 'a::var_TT set"
and
  "REC.CCTOR :: ('a::var_TT, 'a, 'a TT \<times> ('a REC.P \<Rightarrow> 'a REC.C), 'a TT \<times> ('a REC.P \<Rightarrow> 'a REC.C)) F \<Rightarrow> 'a REC.P \<Rightarrow> 'a REC.C"
   = "(\<lambda>F p. cctor (map_F (Rep_ssfun p) id ((\<lambda>R. R p) o snd) ((\<lambda>R. R p) o snd) F)) :: 
  ('a::var_TT, 'a, 'a TT \<times> (('a ssfun) \<Rightarrow> 'a TT), 'a TT \<times> (('a ssfun) \<Rightarrow> 'a TT)) F \<Rightarrow> ('a ssfun) \<Rightarrow> 'a TT"
and
  "REC.mmapC :: ('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a TT \<Rightarrow> 'a REC.C \<Rightarrow> 'a REC.C"
  = "(\<lambda>f _ x. map_TT f x) :: ('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a TT \<Rightarrow> 'a TT \<Rightarrow> 'a TT"
and
  "REC.FFVarsC :: 'a TT \<Rightarrow> 'a::var_TT REC.C \<Rightarrow> 'a set"
  = "(\<lambda>_ x. FFVars x) :: 'a TT \<Rightarrow> 'a::var_TT TT \<Rightarrow> 'a set"
and
  "REC.mapP :: ('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a REC.P \<Rightarrow> 'a REC.P"
   = "(\<lambda>u p. compSS u p) :: ('a::var_TT \<Rightarrow> 'a) \<Rightarrow> ('a ssfun) \<Rightarrow> ('a ssfun)"
and
  "REC.FVarsP :: 'a::var_TT REC.P \<Rightarrow> 'a set"
  = "(\<lambda>p. imsupp (Rep_ssfun p)) :: ('a::var_TT ssfun) \<Rightarrow> 'a set"
       apply -
  subgoal by (rule emp_bound)
  subgoal (* fixed p here? is this a bug? *) 
    using emp_bound imsupp_supp_bound Rep_ssfun by auto 
  subgoal unfolding termLikeStr_def apply safe
    subgoal by simp
    subgoal premises prems for u v
      supply prems[transfer_rule] bij_comp[transfer_rule] supp_comp_bound[transfer_rule]
      by (rule ext, transfer fixing: u v) (auto simp: fun_eq_iff prems o_inv_distrib)
    subgoal premises prems for u p
      supply prems(1,2)[transfer_rule]
      using prems(3)
      apply (transfer fixing: u)
      subgoal for p
        unfolding fun_eq_iff o_apply
        apply (subst imsupp_commute[of u p, unfolded fun_eq_iff o_apply, rule_format])
         apply (auto simp: prems(1) image_iff imsupp_def supp_def)
        by (metis bij_implies_inject prems(1))
      done
    subgoal premises prems for u p a
      supply prems(1,2)[transfer_rule]
      using prems(3)
      apply (transfer fixing: u a)
      subgoal for p
        by (auto simp: supp_def imsupp_def image_iff prems(1) bij_inv_eq_iff[of u, symmetric])
      done
    subgoal premises prems for u p a
      supply prems(1,2)[transfer_rule]
      using prems(3)
      apply (transfer fixing: u a)
      subgoal for p
        by (auto simp: supp_def imsupp_def image_iff prems(1) intro: exI[of _ "u _"])
      done
    done
  subgoal
    apply (auto simp: imsupp_supp_bound FFVars_simps F_set_map supp_id_bound emp_bound Rep_ssfun[simplified])
    using imsupp_def supp_def apply fastforce
    using imsupp_def supp_def apply fastforce
      apply (metis (no_types, hide_lams) UnE fst_conv subset_eq)
     apply (metis (no_types, hide_lams) UnE fst_conv subset_eq)
    apply (metis (no_types, hide_lams) UnE fst_conv subset_eq)
    done
  subgoal
    apply (auto simp: map_TT_cctor compSS.rep_eq F_map_comp[symmetric] Rep_ssfun[simplified]
      supp_comp_bound supp_inv_bound supp_id_bound mmapfn_def inv_o_simp1[THEN rewriteR_comp_comp]
      map_TT_id
      intro!: cctor_eq_intro_map_TT[of id] F_map_cong)
    done
  subgoal
    unfolding termLikeStrC_def apply (intro conjI)
    subgoal by (auto simp: map_TT_id)
    subgoal by (safe, transfer') (auto simp: asSS_def T_map_comp supp_comp_bound)
    subgoal by (safe, transfer') (auto simp: asSS_def supp_id_bound intro!: alpha_bij[of _ _ _ id, unfolded T_map_id] alpha_refl)
    subgoal by (safe; transfer') (auto simp: FVars_map_T asSS_def)
    done
  done

hide_const f

context
  fixes f :: "'a :: var_TT \<Rightarrow> 'a"
  assumes f: "|supp f| <o bound (any :: 'a)"
begin

lift_definition fSS :: "'a ssfun" is f by (rule f)

definition vvsubst where "vvsubst x = ff0 x fSS"

lemma vvsubst_cctor: "set2_F x \<inter> (imsupp f) = {} \<Longrightarrow> nnoclash x \<Longrightarrow>
  vvsubst (cctor x) = cctor (map_F f id vvsubst vvsubst x)"
  unfolding vvsubst_def
  by (subst ff0_cctor)
    (auto simp: F_map_comp[symmetric] f supp_id_bound o_def id_def[symmetric] Rep_ssfun fSS.rep_eq)

lemma FFVars_vvsubst_weak: "FFVars (vvsubst t) \<subseteq> FFVars t \<union> imsupp f"
  unfolding vvsubst_def
  by (rule order_trans[OF ff0_FFVars])
    (auto simp: F_map_comp[symmetric] f supp_id_bound o_def id_def[symmetric] Rep_ssfun fSS.rep_eq)

end

thm vvsubst_cctor FFVars_vvsubst_weak

(* fresnness versus vsubst: *)
theorem FFVars_vvsubst:
  fixes t :: "('a::var_TT)TT"
  assumes supp: "|supp f| <o bound(any::'a)"
  shows "FFVars (vvsubst f t) = {f a1 | a1 . a1 \<in> FFVars t}"
  apply (induct t rule: TT_fresh_induct[consumes 0, of "imsupp f"])
   apply (simp only: imsupp_supp_bound supp)
  apply (subst vvsubst_cctor)
     apply (auto simp: supp nnoclash_def FFVars_simps F_set_map supp_id_bound image_iff)
   apply (auto simp: imsupp_def not_in_supp_alt image_iff)
  apply (metis not_in_supp_alt)
  done

theorem vvsubst_map_TT:
  fixes t :: "('a::var_TT)TT"
  assumes "bij f" "|supp f| <o bound(any::'a)"
  shows "vvsubst f t = map_TT f t"
  apply (induct t rule: TT_fresh_induct[consumes 0, of "imsupp f"])
   apply (simp only: imsupp_supp_bound assms)
  apply (rule box_equals[OF _ sym[OF vvsubst_cctor] sym[OF map_TT_cctor]])
      apply (auto simp only: imsupp_supp_bound assms TT_inject0 F_set_map F_map_comp[symmetric]
      bij_id supp_id_bound image_id id_apply id_o o_id map_TT_id nnoclash_def
      elim!: imsupp_empty_IntD2[rotated, symmetric] intro!: exI[of _ id] F_map_cong)
  done

theorem vvsubst_id: "vvsubst id t = t"
  unfolding vvsubst_map_TT[OF bij_id supp_id_bound] map_TT_id id_apply ..

lemma not_in_imsuppD: "f x \<notin> imsupp f \<Longrightarrow> f x = x"
  by (auto simp: imsupp_def not_in_supp_alt image_iff)

(* Compositonality (bound-restricted functoriality) of vsubst: *)
theorem vvsubst_o:
  fixes t :: "('a::var_TT)TT"
  assumes supp: "|supp g| <o bound(any::'a)" "|supp f| <o bound(any::'a)"
  shows "vvsubst (g o f) t = vvsubst g (vvsubst f t)"
  apply (induct t rule: TT_fresh_induct[consumes 0, of "imsupp g \<union> imsupp f"])
   apply (auto simp only: imsupp_supp_bound supp Un_bound F_set_map nnoclash_def
      F_map_comp[symmetric] bij_id supp_id_bound supp_comp_bound id_apply id_o Un_iff de_Morgan_disj
      FFVars_vvsubst
      intro!: trans[OF vvsubst_cctor] trans[OF _ vvsubst_cctor[symmetric]] trans[OF _ o_apply[symmetric]]
      trans[OF _ arg_cong[of _ _ "vvsubst g", OF vvsubst_cctor[symmetric]]] arg_cong[of _ _ cctor]
      F_map_cong dest!: set_mp[OF imsupp_o]
      | drule meta_spec2, drule meta_mp, assumption, drule meta_mp, assumption)+
   apply (metis Un_iff imsupp_def in_imsupp not_in_supp_alt)
  apply (metis Un_iff imsupp_def in_imsupp not_in_supp_alt)
  done

(* Obliviousness of ssubst w.r.t. fresh variables: *)
theorem vvsubst_cong:
  fixes t :: "('a::var_TT)TT"
  assumes supp: "|supp f| <o bound(any::'a)" "|supp g| <o bound(any::'a)"
    and fr: "\<And> a. a \<in> FFVars t \<Longrightarrow> f a = g a"
  shows "vvsubst f t = vvsubst g t"
  using fr
  apply (induct t rule: TT_fresh_induct[consumes 0, of "imsupp g \<union> imsupp f"])
   apply (simp only: imsupp_supp_bound supp Un_bound)
  subgoal premises prems for x
    apply (insert prems(3-6))
    apply (auto simp only: FFVars_simps supp nnoclash_def
        Un_iff UN_iff Diff_iff de_Morgan_disj de_Morgan_conj supp_id_bound
        intro!: trans[OF vvsubst_cctor] trans[OF _ vvsubst_cctor[symmetric]] trans[OF _ o_apply[symmetric]]
        arg_cong[of _ _ cctor] F_map_cong)
    apply simp
     apply (rule prems(1), assumption, rule prems(6), erule (1) FFVars_intros(2))
    apply (rule prems(2), assumption)
    subgoal for t a apply (cases "a \<in> set2_F x")
       apply (rule box_equals[OF refl imsupp_empty_IntD2[symmetric] imsupp_empty_IntD2[symmetric], of "set2_F x" f a "set2_F x" g])
          apply (auto simp only: | drule meta_spec, erule meta_mp)+
      done
    done
  done

(* Unary var-substitution: *)
definition vusubst :: "('a::var_TT) \<Rightarrow> 'a \<Rightarrow> 'a TT \<Rightarrow> 'a TT" where
  "vusubst a a' t \<equiv> vvsubst (id(a:=a')) t"

(* The next is the simplification rule working with the variable convention: *)
theorem vusubst_cctor:
  assumes "set2_F x \<inter> {a,a'} = {}" "nnoclash x"
  shows "vusubst a a' (cctor x) =  cctor (map_F (id(a := a')) id (vusubst a a') (vusubst a a') x)"
  unfolding vusubst_def using assms
  apply (force simp only: supp_id_upd imsupp_id_fun_upd intro!: vvsubst_cctor split: if_splits)
  done

theorem FFVars_vusubst:
  fixes t :: "('a::var_TT)TT"
  shows "FFVars (vusubst a1 a2 t) = (if a1 \<in> FFVars t then FFVars t - {a1} \<union> {a2} else FFVars t)"
  unfolding vusubst_def
  apply (auto simp only: FFVars_vvsubst supp_id_upd fun_upd_apply id_apply split: if_splits)
  done

theorem vusubst_comp_same:
  fixes t :: "('a::var_TT)TT"
  shows "vusubst a a2 (vusubst a a1 t) = vusubst a ((id(a:=a2)) a1) t"
  unfolding vusubst_def
  apply (auto simp only: vvsubst_o[symmetric] supp_id_upd supp_comp_bound
      o_apply fun_upd_apply id_apply intro!: vvsubst_cong split: if_splits)
  done

theorem vusubst_comp_diff:
  fixes t :: "('a::var_TT)TT"
  assumes diff: "a1 \<noteq> a2" "a1 \<noteq> a2'"
  shows "vusubst a2 a2' (vusubst a1 a1' t) = vusubst a1 ((id(a2:=a2')) a1') (vusubst a2 a2' t)"
  unfolding vusubst_def using diff
  apply (auto simp only: vvsubst_o[symmetric] supp_id_upd supp_comp_bound
      o_apply fun_upd_apply id_apply intro!: vvsubst_cong split: if_splits)
  done

theorem vusubst_idle:
  fixes t :: "('a::var_TT)TT"
  assumes "a \<notin> FFVars t"
  shows "vusubst a a' t = t"
  unfolding vusubst_def using assms
  apply (auto simp only: supp_id_bound supp_id_upd
      fun_upd_apply id_apply intro!: trans[OF vvsubst_cong vvsubst_id] split: if_splits)
  done

definition rel_TT where "rel_TT f = Grp (vvsubst f)"

lemma rel_TT_eq: "rel_TT id = (=)"
  unfolding rel_TT_def vvsubst_id id_def[symmetric] eq_alt[symmetric] ..

lemma TT_rel_compp_le:
  fixes f g :: "'a::var_TT \<Rightarrow> 'a"
  shows "|supp f| <o bound(any::'a) \<Longrightarrow> |supp g| <o bound(any::'a) \<Longrightarrow> rel_TT f OO rel_TT g \<le> rel_TT (g o f)"
  unfolding rel_TT_def by (auto simp: Grp_def vvsubst_o)

lemma TT_inject:
  fixes x x' :: "('a::var_TT, 'a, 'a TT, 'a TT) F"
  shows "(cctor x = cctor x') =
  (\<exists>f. bij f \<and>
       |supp f| <o bound(any::'a) \<and>
       id_on ((\<Union>t\<in>set4_F x. FFVars t) - set2_F x) f \<and>
       map_F id f id (vvsubst f) x = x')"
  unfolding TT_inject0
  apply (rule ex_cong conj_cong refl iffI F_map_cong | erule trans[rotated]
      | auto simp only: supp_id_bound bij_id id_apply vvsubst_map_TT)+
  done

thm \<comment> \<open>MRBNF properties\<close>
  vvsubst_id
  vvsubst_o
  FFVars_vvsubst
  vvsubst_cong
  card_of_FFVars_bound
  bound_card_order
  bound_cinfinite
  rel_TT_def
  rel_TT_eq
  TT_rel_compp_le

end