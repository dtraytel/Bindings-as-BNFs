theory Codatatype_VVsubst
imports Codatatype_Corecursion_Template
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

context
  fixes u v :: "'a :: var_TT \<Rightarrow> 'a"
  assumes [transfer_rule, simp]: "bij u" "|supp u| <o bound(any :: 'a)" "bij v" "|supp v| <o bound(any :: 'a)"
begin

lemma compSS_o[simp]: "compSS (u o v) p = compSS u (compSS v p)"
  supply bij_comp[transfer_rule] supp_comp_bound[transfer_rule]
  apply transfer
  apply (auto simp: o_inv_distrib)
  done

end

lemma compSS_id[simp]: "compSS id = id"
  supply supp_id_bound[transfer_rule] bij_id[transfer_rule] by (rule ext, transfer) auto

theorem TT_fresh_inject:
  fixes x x' :: "('a::vvar_TT, 'a, 'a TT,'a TT) F" and A :: "'a set"
  assumes "|A| <o bound(any::'a)" "set2_F x \<inter> A = {}" "set2_F x' \<inter> A = {}"
  shows "cctor x = cctor x' \<longleftrightarrow>
   (\<exists>f. bij f \<and> |supp f| <o bound(any :: 'a) \<and> id_on (FFVarsB x) f \<and>
        A \<inter> imsupp f = {} \<and> map_F id f id (map_TT f) x = x')" (is "_ \<longleftrightarrow> (\<exists>f. ?renaming f)")
proof
  assume "cctor x = cctor x'"
  then obtain f where "bij f" "|supp f| <o bound(any :: 'a)" "id_on (FFVarsB x) f" "map_F id f id (map_TT f) x = x'"
    unfolding TT_inject0 by blast
  then have "?renaming (avoiding_bij f (FFVarsB x) (set2_F x) A)"
    using avoiding_bij[of f "FFVarsB x" "set2_F x" A] assms
    apply (auto 0 3 simp: var_TT_infinite supp_id_bound F_set_map
      ordLeq_ordLess_trans[OF card_of_diff UNION_bound[OF set4_F_bound card_of_FFVars_bound]] set2_F_bound
      ordLeq_ordLess_trans[OF card_of_diff] intro!: F_map_cong map_TT_cong)
    subgoal for t a
      apply (cases "a \<in> set2_F x")
       apply (fastforce simp: id_on_def)+
      done
    done
  then show "\<exists>f. ?renaming f" by blast
qed (auto simp add: TT_inject0)

template_instance VVSUBST: COREC where
  'a COREC.D = "'a TT \<times> 'a ssfun"
for
  "COREC.DDTOR :: 'a::vvar_TT COREC.D \<Rightarrow> ('a, 'a, 'a TT + 'a COREC.D, 'a TT + 'a COREC.D) F set"
  = "(\<lambda>(t, f). {map_F (Rep_ssfun f) id (\<lambda>x. Inr (x, f)) (\<lambda>x. Inr (x, f)) x | x.
        t = cctor x \<and> set2_F x \<inter> imsupp (Rep_ssfun f) = {}}) :: 
  ('a::vvar_TT TT \<times> 'a ssfun \<Rightarrow> ('a, 'a, 'a TT + 'a TT \<times> 'a ssfun , 'a TT + 'a TT \<times> 'a ssfun) F set)"
  and
  "COREC.mmapD :: ('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'a COREC.D \<Rightarrow> 'a COREC.D"
  = "(\<lambda>u (x, f). (map_TT u x, compSS u f)) :: ('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'a TT \<times> 'a ssfun \<Rightarrow> 'a TT \<times> 'a ssfun"
  and
  "COREC.FFVarsD :: 'a::vvar_TT COREC.D \<Rightarrow> 'a set"
  = "(\<lambda>(x, f). FFVars x \<union> imsupp (Rep_ssfun f)) :: 'a::vvar_TT TT \<times> 'a ssfun \<Rightarrow> 'a set"
      apply -
  subgoal
    by (auto split: prod.splits simp: fresh_nchotomy imsupp_supp_bound Rep_ssfun[simplified])
  subgoal
    apply clarsimp
    subgoal for p x y
      apply (subst (asm) TT_fresh_inject[of "imsupp (Rep_ssfun p)"])
         apply (auto simp: imsupp_supp_bound Rep_ssfun[simplified]) [3]
      apply safe
      subgoal for u
        apply (auto simp: supp_inv_bound supp_id_bound supp_comp_bound Rep_ssfun[simplified]
            F_set_map FFVars_map_TT F_map_comp[symmetric] id_on_def
            map_TT_id map_TT_comp[symmetric] bij_imp_inv
            intro!: exI[of _ "inv u"] F_map_cong)
         apply (auto simp: imsupp_def supp_def) []
        subgoal premises prems
          supply prems(6,7)[transfer_rule] supp_inv_bound[transfer_rule] bij_imp_bij_inv[transfer_rule]
          using prems(4,5,8,9)
          apply (transfer fixing: u)
          apply (auto simp: prems(6,7) fun_eq_iff)
          subgoal for x p a
            apply (auto simp: imsupp_commute[THEN fun_cong, simplified, of p u a] prems(6))
            done
          done
        done
      done
    done
  subgoal
    apply (auto simp: F_set_map supp_id_bound Rep_ssfun[simplified] FFVars_simps)
     apply (auto simp: imsupp_def supp_def)
    done
  subgoal
    apply (simp split: prod.splits, safe)
    subgoal for t p _ x
      apply (drule arg_cong[of _ _ "map_TT (inv u)"])
      apply (auto simp: image_iff map_TT_comp[symmetric] supp_inv_bound map_TT_id map_TT_cctor)
      apply (rule exI conjI refl)+
       apply (auto simp: F_map_comp[symmetric] supp_id_bound Rep_ssfun[simplified]
          image_iff map_sum_def compSS.rep_eq supp_comp_bound supp_inv_bound F_set_map
          inv_o_simp1[THEN rewriteR_comp_comp] map_TT_comp[symmetric] map_TT_id
          split: sum.splits intro!: F_map_cong)
      apply (frule (1) imsupp_empty_IntD2)
      apply (auto simp: imsupp_def supp_def bij_inv_rev bij_imp_inv disjoint_iff_not_equal
          ball_Un)
      apply (drule bspec, assumption)
      apply (auto simp: bij_imp_inv[symmetric, of u])
      subgoal for x
        apply (auto dest!: spec[of _ "u x"])
        done
      done
    done
  subgoal
    apply (auto simp: map_TT_id map_TT_comp)
    done
  done

hide_const f

context
  fixes f :: "'a :: vvar_TT \<Rightarrow> 'a"
  assumes f: "|supp f| <o bound (any :: 'a)"
begin

lift_definition fSS :: "'a ssfun" is f by (rule f)

definition vvsubst where "vvsubst x = ff0 (x, fSS)"

lemma vvsubst_cctor: "set2_F x \<inter> imsupp f = {} \<Longrightarrow>
  vvsubst (cctor x) = cctor (map_F f id vvsubst vvsubst x)"
  unfolding vvsubst_def
  by (subst ff0_DDTOR)
    (auto simp: F_map_comp[symmetric] f supp_id_bound o_def id_def[symmetric] Rep_ssfun fSS.rep_eq)

lemma FFVars_vvsubst_weak: "FFVars (vvsubst t) \<subseteq> FFVars t \<union> imsupp f"
  unfolding vvsubst_def
  by (rule order_trans[OF ff0_FFVarsD])
    (auto simp: F_map_comp[symmetric] f supp_id_bound o_def id_def[symmetric] Rep_ssfun fSS.rep_eq)

end

thm vvsubst_cctor FFVars_vvsubst_weak

lemma map_TT_vvsubst:
  fixes f u :: "'a :: vvar_TT \<Rightarrow> 'a"
  assumes f: "|supp f| <o bound (any :: 'a)" and u: "bij u" "|supp u| <o bound (any :: 'a)"
  shows "map_TT u (vvsubst f t) = vvsubst (u o f o inv u) (map_TT u t)"
  unfolding vvsubst_def[OF f] ff0_mmapD[OF u, symmetric]
  by (auto simp: vvsubst_def assms ff0_mmapD[symmetric] supp_comp_bound supp_inv_bound
    fSS_def compSS_def Abs_ssfun_inverse)

lemma FFVars_vvsubst_le:
  "a \<in> FFVars u \<Longrightarrow> \<forall>x (f :: 'a::vvar_TT \<Rightarrow> 'a).
   u = vvsubst f (cctor x) \<longrightarrow> |supp f| <o bound(any::'a) \<longrightarrow> set2_F x \<inter> imsupp f = {} \<longrightarrow>
   a \<in> f ` FFVars (cctor x)"
  apply (induct a u rule: FFVars_induct[rule_format, consumes 1]; (rule allI impI)+)
  subgoal for a fx x f
    apply (auto simp only: F_set_map vvsubst_cctor
        bij_id supp_id_bound imsupp_supp_bound TT_inject0 image_id id_apply
        dest!: arg_cong[of _ _ set1_F]
        intro!: imageI FFVars_intros(1))
    done
  subgoal for fx u a x f
    apply (auto simp only: F_set_map TT_inject0 vvsubst_cctor
        supp_id_bound bij_id image_id id_apply dest!: arg_cong[of _ _ set3_F])
    subgoal for v y
      apply (rule fresh_cases[of "imsupp f" y])
       apply (simp only: imsupp_supp_bound)
      apply (drule spec2, drule mp, hypsubst, rule refl)
      apply (auto simp only: intro!: imageI FFVars_intros(2))
      done
    done
  subgoal for fx u a x f
    apply (auto simp only: F_set_map TT_inject0 vvsubst_cctor
        supp_id_bound bij_id image_id id_apply)
    apply (frule arg_cong[of _ _ set2_F, symmetric])
    apply (drule arg_cong[of _ _ set4_F])
    apply (auto simp only: F_set_map TT_inject0 vvsubst_cctor
        supp_id_bound bij_id image_id id_apply)
    subgoal for v
      apply (drule arg_cong[of _ _ "image (map_TT (inv v))"])
      apply (auto simp: image_image map_TT_comp[symmetric] map_TT_id supp_inv_bound
          map_TT_vvsubst)
      subgoal for y
        apply (rule fresh_cases[of "imsupp f" y])
         apply (simp only: imsupp_supp_bound)
        apply (hypsubst)
        apply (auto simp: map_TT_cctor supp_inv_bound)
        apply (drule spec2, drule mp, rule refl)
        apply (drule mp)
         apply (simp only: supp_comp_bound supp_inv_bound)
        apply (drule mp)
         apply (auto simp: F_set_map supp_inv_bound) []
         apply (auto simp: imsupp_def supp_def bij_imp_inv') []
        apply (auto simp: map_TT_cctor[symmetric] supp_inv_bound FFVars_map_TT)
        apply (auto intro!: image_eqI[rotated, OF FFVars_intros(3)])
        using imsupp_empty_IntD2 apply fastforce
        apply (auto simp: id_on_def)
        done
      done
    done
  done

lemma FFVars_vvsubst_ge:
  fixes f::"'a::vvar_TT\<Rightarrow>'a"
  assumes "|supp f| <o bound(any::'a)"
  shows "a \<in> FFVars t \<Longrightarrow>  \<forall>x g. |supp g| <o bound(any::'a) \<longrightarrow> bij g  \<longrightarrow> g a = a \<longrightarrow>
    t = map_TT (inv g) (cctor x) \<longrightarrow> set2_F x \<inter> imsupp f = {} \<longrightarrow>
    f a \<in> FFVars (vvsubst f (cctor x))"
  apply (induct rule: FFVars_induct[rule_format, consumes 1]; (rule allI impI)+)
  subgoal
    apply (auto simp: vvsubst_cctor assms F_set_map supp_id_bound supp_inv_bound TT_inject0
        map_TT_cctor image_iff bij_inv_rev dest!: arg_cong[of _ _ set1_F] intro!: FFVars_intros(1))
    done
  subgoal for fx t a x g
    apply (auto simp: vvsubst_cctor assms F_set_map supp_id_bound supp_inv_bound imsupp_supp_bound
        TT_inject0 map_TT_cctor FFVars_map_TT dest!: arg_cong[of _ _ set3_F])
    subgoal for v u
      apply (rule fresh_cases[of "imsupp f" u])
       apply (simp only: imsupp_supp_bound assms)
      subgoal for y
        apply (drule spec2[of _ y g])
        apply (auto simp: vvsubst_cctor bij_inv_rev map_TT_cctor supp_id_bound supp_inv_bound F_set_map assms
            intro!: FFVars_intros(2))
        done
      done
    done
  subgoal for fx t a x g
    apply (auto simp: vvsubst_cctor assms F_set_map supp_id_bound supp_inv_bound imsupp_supp_bound
        TT_inject0 map_TT_cctor FFVars_map_TT)
    apply (frule arg_cong[of _ _ set2_F])
    apply (drule arg_cong[of _ _ set4_F])
    apply (auto simp: vvsubst_cctor assms F_set_map supp_id_bound supp_inv_bound imsupp_supp_bound
        TT_inject0 map_TT_cctor FFVars_map_TT)
    subgoal for h
      apply (drule id_onD[of _ h a])
       apply auto []
      apply (drule arg_cong[of "h ` _" _ "image (inv h)"])
      apply (drule arg_cong[of "map_TT h ` _" _ "image (map_TT (inv h))"])
      apply (auto simp: image_image map_TT_comp[symmetric] map_TT_id supp_inv_bound
          FFVars_map_TT)
      subgoal for u
        apply (rule fresh_cases[of "imsupp f" u])
         apply (simp only: imsupp_supp_bound assms)
        subgoal for y
          apply (drule spec2[of _ y "g o h"])
          apply (simp only: supp_comp_bound bij_comp simp_thms map_TT_cctor
              o_inv_distrib supp_inv_bound bij_imp_bij_inv o_apply[of g h a])
          apply (auto simp: F_set_map supp_id_bound assms vvsubst_cctor
              imsupp_empty_IntD1 image_iff bij_inv_rev bij_imp_inv
              dest!: bspec[of _ _ a] intro!: FFVars_intros(3))
          done
        done
      done
    done
  done

(* fresnness versus vsubst: *)
theorem FFVars_vvsubst:
  fixes t :: "('a::vvar_TT)TT" and f :: "'a \<Rightarrow> 'a"
  assumes supp: "|supp f| <o bound(any::'a)"
  shows "FFVars (vvsubst f t) = f ` FFVars t"
  using imsupp_supp_bound[THEN iffD2, OF supp]
proof (cases rule: fresh_cases[of _ t])
  case (1 x)
  show ?thesis
    unfolding \<open>t = cctor x\<close>
    apply (rule set_eqI iffI)+
     apply (erule FFVars_vvsubst_le[rule_format, OF _ refl, of _ f x];
        simp only: supp imsupp_supp_bound 1)
    apply (erule imageE)
    apply hypsubst
    apply (rule FFVars_vvsubst_ge[rule_format, of f _ t id])
         apply (auto simp: 1 supp_id_bound supp map_TT_id)
    done
qed

theorem vvsubst_map_TT:
  fixes t :: "('a::vvar_TT)TT"
  assumes "bij f" "|supp f| <o bound(any::'a)"
  shows "vvsubst f t = map_TT f t"
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (rule fresh_cases[of "imsupp f" t])
     apply (simp only: imsupp_supp_bound assms)
    apply (simp only: imsupp_supp_bound assms vvsubst_cctor map_TT_cctor)
    apply (rule exI conjI refl)+
      apply (auto simp only: F_rel_map assms supp_inv_bound bij_imp_bij_inv inv_o_simp1
      bij_id supp_id_bound image_id id_apply o_id map_TT_id imsupp_inv bij_inv_rev relcompp_apply Grp_def
      elim!: imsupp_empty_IntD2[symmetric] intro!: exI[of _ id]
      F_rel_mono_strong0[rotated 6, OF F.rel_eq[THEN predicate2_eqD, THEN iffD2], OF refl])
    done
  done

theorem vvsubst_id: "vvsubst id t = t"
  unfolding vvsubst_map_TT[OF bij_id supp_id_bound] map_TT_id id_apply ..

(* Compositonality (bound-restricted functoriality) of vsubst: *)
theorem vvsubst_o:
  fixes t :: "('a::vvar_TT)TT"
  assumes supp: "|supp g| <o bound(any::'a)" "|supp f| <o bound(any::'a)"
  shows "vvsubst (g o f) t = vvsubst g (vvsubst f t)"
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (rule fresh_cases[of "imsupp f \<union> imsupp g" t])
     apply (auto simp only: Un_bound imsupp_supp_bound assms vvsubst_cctor
        imsupp_disj_comp Int_Un_distrib F_set_map bij_id supp_id_bound supp_comp_bound
        image_id id_apply)
    apply (rule exI conjI refl)+
    apply (auto simp only: F_rel_map F_map_comp[symmetric]
        assms bij_id supp_id_bound supp_comp_bound id_o)
    apply (rule F_rel_mono_strong0[rotated 6, OF F_rel_map_right[rotated 6, OF F.rel_refl[of "(=)" "(=)"]]])
                     apply (auto simp only: o_apply id_apply id_def[symmetric] supp_comp_bound supp_id_bound bij_id assms F_set_map Grp_def id_o)
    done
  done

(* Obliviousness of ssubst w.r.t. fresh variables: *)
theorem vvsubst_cong:
  fixes t :: "('a::vvar_TT)TT"
  assumes supp: "|supp f| <o bound(any::'a)" "|supp g| <o bound(any::'a)"
    and fr: "\<And> a. a \<in> FFVars t \<Longrightarrow> f a = g a"
  shows "vvsubst f t = vvsubst g t"
  using fr
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (rule fresh_cases[of "imsupp f \<union> imsupp g" t])
     apply (auto simp only: Un_bound imsupp_supp_bound assms vvsubst_cctor Int_Un_distrib)
    apply (rule exI conjI refl)+
    apply (auto simp only: F_rel_map F_map_comp[symmetric]
        assms bij_id supp_id_bound supp_comp_bound id_o)
    apply (rule F_rel_mono_strong0[rotated 6, OF F_rel_map_right[rotated 6, OF F.rel_refl[of "(=)" "(=)"]]])
                     apply (auto simp only: o_apply id_apply id_def[symmetric] supp_comp_bound supp_id_bound bij_id
        assms F_set_map FFVars_simps relcompp_apply id_o Un_iff UN_iff imp_disjL all_conj_distrib)
    subgoal
      apply (simp only: Grp_def simp_thms UNIV_I)
      apply (rule disjI1 exI conjI refl)+
      apply (auto simp only:)
      done
    subgoal
      apply (simp only: Grp_def simp_thms UNIV_I)
      apply (rule disjI1 exI conjI refl)+
      apply (auto simp only: dest!: imsupp_empty_IntD2)
      done
    done
  done

(* Unary var-substitution: *)
definition vusubst :: "('a::vvar_TT) \<Rightarrow> 'a \<Rightarrow> 'a TT \<Rightarrow> 'a TT" where
  "vusubst a a' t \<equiv> vvsubst (id(a:=a')) t"

(* The next is the simplification rule working with the variable convention: *)
theorem vusubst_cctor:
  assumes "set2_F x \<inter> {a,a'} = {}"
  shows "vusubst a a' (cctor x) =  cctor (map_F (id(a := a')) id (vusubst a a') (vusubst a a') x)"
  unfolding vusubst_def using assms
  apply (force simp only: supp_id_upd imsupp_id_fun_upd intro!: vvsubst_cctor split: if_splits)
  done

theorem FFVars_vusubst:
  fixes t :: "('a::vvar_TT)TT"
  shows "FFVars (vusubst a1 a2 t) = (if a1 \<in> FFVars t then FFVars t - {a1} \<union> {a2} else FFVars t)"
  unfolding vusubst_def
  apply (auto simp only: FFVars_vvsubst supp_id_upd fun_upd_apply id_apply split: if_splits)
  done

theorem vusubst_comp_same:
  fixes t :: "('a::vvar_TT)TT"
  shows "vusubst a a2 (vusubst a a1 t) = vusubst a ((id(a:=a2)) a1) t"
  unfolding vusubst_def
  apply (auto simp only: vvsubst_o[symmetric] supp_id_upd supp_comp_bound
      o_apply fun_upd_apply id_apply intro!: vvsubst_cong split: if_splits)
  done

theorem vusubst_comp_diff:
  fixes t :: "('a::vvar_TT)TT"
  assumes diff: "a1 \<noteq> a2" "a1 \<noteq> a2'"
  shows "vusubst a2 a2' (vusubst a1 a1' t) = vusubst a1 ((id(a2:=a2')) a1') (vusubst a2 a2' t)"
  unfolding vusubst_def using diff
  apply (auto simp only: vvsubst_o[symmetric] supp_id_upd supp_comp_bound
      o_apply fun_upd_apply id_apply intro!: vvsubst_cong split: if_splits)
  done

theorem vusubst_idle:
  fixes t :: "('a::vvar_TT)TT"
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
  fixes f g :: "'a::vvar_TT \<Rightarrow> 'a"
  shows "|supp f| <o bound(any::'a) \<Longrightarrow> |supp g| <o bound(any::'a) \<Longrightarrow> rel_TT f OO rel_TT g \<le> rel_TT (g o f)"
  unfolding rel_TT_def by (auto simp: Grp_def vvsubst_o)

lemma TT_inject:
  fixes x x' :: "('a::vvar_TT, 'a, 'a TT, 'a TT) F"
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