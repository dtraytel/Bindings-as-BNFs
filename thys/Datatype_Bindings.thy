theory Datatype_Bindings
  imports Common_Data_Codata_Bindings
begin  

(* The type T of pre-terms: In ('a, 'a, 'a T, 'a T) F:
-- the first component 'a represents the free variables
-- the second component 'a represents the binding variables
-- the third (recursive) component of 'a T is free, i.e., not bound by the second component
-- the fourth (recursive) component 'a T is bound by the second component
*)

datatype 'a::var_TT T = ctor "('a, 'a, 'a T, 'a T) F"

(* T acts like a BNF on bijections; but the BNF package did not infer this,
since P is not a BNF; so we need to do the constructions ourselves: *)

primrec map_T :: "('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a T \<Rightarrow> 'a T" where
  "map_T u (ctor x) = ctor (map_F u u id id (map_F id id (map_T u) (map_T u) x))"

lemma map_T_simps:
  fixes u::"'a::var_TT\<Rightarrow>'a" assumes u: "bij u" "|supp u| <o bound(any::'a)"
  shows "map_T u (ctor x) = ctor (map_F u u(map_T u) (map_T u) x)"
  using assms by (simp add: F_map_comp[symmetric] supp_id_bound)

declare map_T.simps[simp del]

lemma T_map_id: "map_T id t = t"
  by (induction t rule: T.induct)
    (auto intro!: trans[OF F_map_cong F_map_id[THEN fun_cong], THEN trans[OF _ id_apply]]
      simp only: map_T_simps bij_id id_def[symmetric] id_apply supp_id_bound)

lemma T_map_comp:
  fixes u::"'a::var_TT\<Rightarrow>'a" and v::"'a::var_TT\<Rightarrow>'a"
  assumes u: "bij u" "|supp u| <o bound(any::'a)" and v: "bij v" "|supp v| <o bound(any::'a)"
  shows "map_T (v o u) t = map_T v (map_T u t)"
  by (induction t rule: T.induct)
    (auto simp only: assms F_map_comp[symmetric] bij_comp supp_comp_bound map_T_simps o_apply o_def[of v u,symmetric]
      intro!: F_map_cong)

inductive free :: "'a::var_TT \<Rightarrow> 'a T \<Rightarrow> bool" where
  set1:      "a \<in> set1_F x \<Longrightarrow> free a (ctor x)"
| set2_free: "t \<in> set3_F x \<Longrightarrow> free a t \<Longrightarrow> free a (ctor x)"
| set2_rec:  "t \<in> set4_F x \<Longrightarrow> a \<notin> set2_F x \<Longrightarrow> free a t \<Longrightarrow> free a (ctor x)"

(* Note: free was just an auxiliary -- we will only use FVars *)
definition FVars :: "'a::var_TT T \<Rightarrow> 'a set" where
  FVars_def: "FVars t = {a . free a t}"

lemma free_FVars: "free a t \<longleftrightarrow> a \<in> FVars t"
  unfolding FVars_def by simp


(* BEGIN emancipation of FVars *)
lemmas FVars_intros = free.intros[unfolded free_FVars]

lemmas FVars_induct[consumes 1, case_names set1 set2_free set2_rec, induct set: FVars] =
  free.induct[unfolded free_FVars]

lemmas FVars_cases[consumes 1, case_names set1 set2_free set2_rec, cases set: FVars] =
  free.cases[unfolded free_FVars]

lemma FVars_ctor:
  "FVars (ctor x) = set1_F x \<union> (\<Union>tt \<in> set3_F x. FVars tt) \<union> ((\<Union>tt \<in> set4_F x. FVars tt) - set2_F x)"
  by (auto elim: FVars_cases intro: FVars_intros)

(* DONE with emancipation of FVars *)

lemma FVars_map_T_le:
  fixes u::"'a::var_TT\<Rightarrow>'a" assumes u: "bij u" "|supp u| <o bound(any::'a)"
  shows "a \<in> FVars t \<Longrightarrow> u a \<in> FVars (map_T u t)"
  apply (induct a t rule: FVars_induct)
  subgoal by (auto simp: assms map_T_simps F_set_map intro!: FVars_intros(1))
  subgoal by (auto simp: assms map_T_simps F_set_map intro!: FVars_intros(2))
  subgoal by (auto simp: assms map_T_simps F_set_map intro!: FVars_intros(3))
  done

lemma FVars_map_T:
  fixes u::"'a::var_TT\<Rightarrow>'a" assumes u: "bij u" "|supp u| <o bound(any::'a)"
  shows "FVars (map_T u t) = u ` FVars t"
  apply (rule set_eqI iffI)+
   apply (drule FVars_map_T_le[OF bij_imp_bij_inv[OF u(1)] supp_inv_bound[OF u]];
      (simp only: T_map_comp[symmetric] supp_inv_bound bij_imp_bij_inv inv_o_simp1
        simp_thms T_map_id u inv_simp2 | erule image_eqI[rotated])+)
  apply (erule imageE, drule FVars_map_T_le[OF u], simp only:)
  done

(* Getting enough variables  *)

lemma card_of_FVars_bound: "|FVars t| <o bound(any::'a::var_TT)"
  apply (induct t rule: T.induct)
  subgoal for t
    apply (auto simp only: FVars_ctor
        intro!: Un_bound UNION_bound set1_F_bound set2_F_bound set3_F_bound set4_F_bound
        ordLeq_ordLess_trans[OF card_of_diff])
    done
  done


(* Alpha Equivalence *)

abbreviation "FVarsB x \<equiv> UNION (set4_F x) FVars - set2_F x"


coinductive alpha:: "'a::var_TT T \<Rightarrow> 'a T \<Rightarrow> bool"
  where alpha: "|supp f| <o bound(any::'a) \<Longrightarrow> bij f \<Longrightarrow> id_on (FVarsB x) f \<Longrightarrow>
    rel_F id f alpha (\<lambda>s s'. alpha (map_T f s) s') x y \<Longrightarrow> alpha (ctor x) (ctor y)"
    monos F_rel_mono[OF supp_id_bound] conj_context_mono
  
lemmas alpha_def_from_paper = alpha.intros[unfolded rel_F_def]
   
(*  rrel_F alpha (\<lambda>s s'. alpha (map_T f s) s') (map_F id f id id x) y  *)

lemma alpha_refl:
  "alpha t t"
  apply (coinduction arbitrary: t rule: alpha.coinduct)
  subgoal for t
    apply (cases t)
    apply (auto simp only: supp_id_bound T_map_id T.inject ex_simps simp_thms
        intro!: F.rel_refl_strong alpha exI[of _ id])
    done
  done

lemma alpha_bij:
  fixes u :: "'a::var_TT\<Rightarrow> 'a" and v :: "'a::var_TT\<Rightarrow> 'a"
  assumes "alpha t t'" "\<forall>x \<in> FVars t. u x = v x" "bij u" "|supp u| <o bound(any::'a)" "bij v" "|supp v| <o bound(any::'a)"
  shows "alpha (map_T u t) (map_T v t')"
  using assms
  apply (coinduction arbitrary: t t' u v rule: alpha.coinduct)
  subgoal for t t' u v
    apply (elim alpha.cases)
    subgoal for f x y
      apply (rule exI[of _ "v o f o inv u"])
      apply (auto simp only: map_T_simps supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv
          F_rel_map supp_id_bound bij_id o_assoc o_id id_o inv_o_simp1 FVars_ctor FVars_map_T
          id_on_def F_set_map o_apply image_iff bij_implies_inject inv_simp1 bex_triv_one_point2
          Ball_def Un_iff Diff_iff UN_iff id_apply bij_inv_rev vimage2p_Grp[symmetric] vimage2p_def
          imp_conjL[symmetric] T_map_comp[symmetric] T.inject simp_thms ex_simps
          elim!: F_rel_mono_strong0[rotated 6])+
        apply (auto 0 3 simp only:) []
       apply (rule exI conjI refl | assumption | auto simp only: o_assoc[symmetric] inv_o_simp1 o_id T_map_comp)+
      done
    done
  done

lemma alpha_bij_eq:
  fixes u :: "'a::var_TT\<Rightarrow> 'a"
  assumes "bij u"  "|supp u| <o bound(any::'a)"
  shows "alpha (map_T u t) (map_T u t') = alpha t t'"
  apply (rule iffI)
   apply (drule alpha_bij[OF _ _ bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms] bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]];
      auto simp only: assms T_map_comp[symmetric] T_map_id supp_inv_bound bij_imp_bij_inv inv_o_simp1)
  apply (erule alpha_bij[OF _ _ assms assms]; simp)
  done

lemma alpha_bij_eq_inv:
  fixes u :: "'a::var_TT\<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o bound(any::'a)"
  shows "alpha (map_T u t1) t2 = alpha t1 (map_T (inv u) t2)"
  apply (subst T_map_comp[of "inv u" "u" t2, unfolded inv_o_simp2[OF u(1)] T_map_id])
      apply (auto simp only: assms bij_imp_bij_inv supp_inv_bound alpha_bij_eq)
  done

lemma alpha_FVars_le:
  "x \<in> FVars t \<Longrightarrow> alpha t t' \<Longrightarrow> x \<in> FVars t'"
  apply (induct x t arbitrary: t' rule: FVars_induct; elim alpha.cases)
    apply (simp_all only: T.inject FVars_ctor)
    apply (rule UnI1, rule UnI1)
    apply (drule rel_funD[OF F_set_transfer(1)[OF supp_id_bound], rotated -1];
      auto simp only: Grp_UNIV_id image_id)
   apply (rule UnI1, rule UnI2)
   apply (drule rel_funD[OF F_set_transfer(3)[OF supp_id_bound], rotated -1];
      auto 0 3 simp only: rel_set_def)
  apply (rule UnI2)
  apply (frule rel_funD[OF F_set_transfer(2)[OF supp_id_bound], rotated -1]; (simp only: Grp_def)?)
  apply (drule conjunct1)
  apply (drule rel_funD[OF F_set_transfer(4)[OF supp_id_bound], rotated -1]; (simp only: rel_set_def)?)
  apply (erule conjE)
  apply (drule bspec, assumption, erule bexE)
  apply (drule alpha_bij_eq_inv[THEN iffD1, rotated -1]; (simp only: )?)
  apply (drule meta_spec, drule meta_mp, assumption)
  apply (simp only: FVars_map_T bij_imp_bij_inv supp_inv_bound)
  apply (rule DiffI)
   apply (erule UN_I)
   apply (auto simp only: id_on_def Diff_iff Union_iff bex_simps
      inv_simp2 bij_implies_inject)
  done

lemma alpha_FVars_le':
  "x \<in> FVars t' \<Longrightarrow> alpha t t' \<Longrightarrow> x \<in> FVars t"
  apply (induct x t' arbitrary: t rule: FVars_induct; elim alpha.cases)
    apply (simp_all only: T.inject FVars_ctor)
    apply (rule UnI1, rule UnI1)
    apply (drule rel_funD[OF F_set_transfer(1)[OF supp_id_bound], rotated -1];
      auto simp only: Grp_UNIV_id image_id)
   apply (rule UnI1, rule UnI2)
   apply (drule rel_funD[OF F_set_transfer(3)[OF supp_id_bound], rotated -1];
      auto 0 3 simp only: rel_set_def)
  apply (rule UnI2)
  apply (frule rel_funD[OF F_set_transfer(2)[OF supp_id_bound], rotated -1]; (simp only: Grp_def)?)
  apply (drule conjunct1)
  apply (drule rel_funD[OF F_set_transfer(4)[OF supp_id_bound], rotated -1]; (simp only: rel_set_def)?)
  apply (erule conjE)
  apply (drule bspec, assumption, erule bexE)
  apply (drule meta_spec, drule meta_mp, assumption)
  apply (simp only: FVars_map_T bij_imp_bij_inv supp_inv_bound image_iff bex_simps)
  apply (erule bexE)
  apply hypsubst
  apply (simp only: id_on_def)
  apply (frule spec, drule mp, rule DiffI, rule UN_I, assumption, assumption)
   apply (auto simp only: )
  done

lemma alpha_FVars:
  "alpha t t' \<Longrightarrow>  FVars t = FVars t'"
  apply (rule set_eqI iffI)+
   apply (erule alpha_FVars_le, assumption)
  apply (erule alpha_FVars_le', assumption)
  done


lemma alpha_sym:
  "alpha t t' \<Longrightarrow> alpha t' t"
  apply (coinduction arbitrary: t t' rule: alpha.coinduct)
  apply (elim alpha.cases; hypsubst)
  subgoal for _ _ f x y
    apply (rule exI[of _ "inv f"] exI conjI refl)+
     apply (rule supp_inv_bound; assumption)
    apply (rule conjI)
     apply (erule bij_imp_bij_inv)
    apply (rule conjI[rotated])
     apply (rule F_rel_flip[THEN iffD1])
         apply (auto simp only: supp_inv_bound bij_imp_bij_inv id_on_inv alpha_bij_eq_inv
        inv_id supp_id_bound inv_inv_eq elim!: F_rel_mono_strong0[rotated 6]) [5]
    apply (frule rel_funD[OF F_set_transfer(2)[OF supp_id_bound], rotated -1]; (simp only: Grp_def)?)
    apply (drule conjunct1)
    apply (drule rel_funD[OF F_set_transfer(4)[OF supp_id_bound], rotated -1]; (simp only: FVars_map_T)?)
    apply (drule rel_set_mono[OF predicate2I, THEN predicate2D, rotated -1])
     apply (erule alpha_FVars)
    apply (drule rel_set_UN_D[symmetric])
    apply (simp only: image_UN[symmetric] FVars_map_T image_set_diff[symmetric] bij_is_inj
        id_on_image id_on_inv)
    done
  done

lemma alpha_trans:
  "alpha t s \<Longrightarrow> alpha s r \<Longrightarrow> alpha t r"
  apply (coinduction arbitrary: t s r rule: alpha.coinduct)
  apply (elim alpha.cases; hypsubst_thin, unfold T.inject)
  subgoal for _ _ _ f x _ g y z
    apply (rule exI[of _ "g o f"])
    apply (rule exI[of _ "x"])
    apply (rule exI[of _ "z"])
    apply (auto simp only: supp_comp_bound bij_comp id_on_comp
        supp_id_bound T_map_comp alpha_bij_eq_inv[of g] ex_simps simp_thms
        elim!: F_rel_mono[THEN predicate2D, rotated -1, OF F_rel_comp_leq[THEN predicate2D],
          of id id, unfolded id_o, rotated 6, OF relcomppI])
     apply (frule rel_funD[OF F_set_transfer(2)[OF supp_id_bound], rotated -1]; (simp only: Grp_def)?)
     apply (drule conjunct1)
     apply (drule rel_funD[OF F_set_transfer(4)[OF supp_id_bound], rotated -1]; (simp only: FVars_map_T)?)
     apply (drule rel_set_mono[OF predicate2I, THEN predicate2D, rotated -1])
      apply (erule alpha_FVars)
     apply (drule rel_set_UN_D[THEN sym])
     apply (simp only: image_UN[symmetric] FVars_map_T image_set_diff[symmetric] bij_is_inj)
    subgoal for xx yy zz
      apply (rule exI[of _ "map_T g zz"])
      apply (auto simp only: inv_o_simp1 T_map_id T_map_comp[symmetric] bij_imp_bij_inv supp_inv_bound alpha_bij_eq_inv[of g])
      done
    done
  done

(* Some refreshments... *)

lemmas card_of_FVarsB_bound =
  ordLeq_ordLess_trans[OF card_of_diff UNION_bound[OF set4_F_bound card_of_FVars_bound]]

lemma refresh_set2_F:
  fixes t :: "('a::var_TT) T" and x :: "('a, 'a, 'a T, 'a T) F" assumes A: "|A::'a set| <o bound(any::'a)"
  shows "\<exists> f. |supp f| <o bound(any::'a) \<and> bij f \<and> id_on (FVarsB x) f \<and> set2_F (map_F id f id (map_T f) x) \<inter> A = {}"
  apply (insert card_of_ordLeq[THEN iffD2, OF ordLess_imp_ordLeq, of "set2_F x \<inter> A" "UNIV - (set2_F x \<union> FVarsB x \<union> A)"])
  apply (drule meta_mp)
   apply (rule ordLess_ordIso_trans)
    apply (rule ordLeq_ordLess_trans[OF card_of_mono1[OF Int_lower1]])
    apply (rule set2_F_bound)
   apply (rule ordIso_symmetric)
   apply (rule infinite_UNIV_card_of_minus[OF var_TT_infinite])
   apply (rule Un_bound[OF Un_bound[OF set2_F_bound card_of_FVarsB_bound] A])
  apply (erule exE conjE)+
  subgoal for u
    apply (insert extU[of u "set2_F x \<inter> A" "u ` (set2_F x \<inter> A)"])
    apply (rule exI[of _ "extU (set2_F x \<inter> A) (u ` (set2_F x \<inter> A)) u"])
    apply (drule meta_mp)
     apply (erule inj_on_imp_bij_betw)
    apply (drule meta_mp)
     apply auto []
    apply (erule conjE)+
    apply (rule context_conjI)
     apply (erule ordLeq_ordLess_trans[OF card_of_mono1])
     apply (rule Un_bound)
      apply (rule ordLeq_ordLess_trans[OF card_of_mono1[OF Int_lower1]])
      apply (rule set2_F_bound)
     apply (rule ordLeq_ordLess_trans[OF card_of_image])
     apply (rule ordLeq_ordLess_trans[OF card_of_mono1[OF Int_lower1]])
     apply (rule set2_F_bound)
    apply (rule conjI)
     apply assumption
    apply (rule conjI)
     apply (erule id_on_antimono)
     apply blast
    apply (auto simp only: F_set_map supp_id_bound)
    subgoal
       apply (auto simp only: extU_def split: if_splits)
      done
    done
  done

inductive subshape :: "'a::var_TT T \<Rightarrow> 'a T \<Rightarrow> bool" where
  "bij u \<Longrightarrow> |supp u| <o bound(any::'a) \<Longrightarrow> alpha (map_T u tt) uu \<Longrightarrow> uu \<in> set3_F x \<union> set4_F x \<Longrightarrow>
  subshape tt (ctor x)"

lemma subshape_induct_raw:
  assumes IH: "\<And> t::'a::var_TT T. (\<And> tt. subshape tt t \<Longrightarrow> P tt) \<Longrightarrow> P t"
  shows "bij g \<Longrightarrow> |supp g| <o bound(any::'a) \<Longrightarrow> alpha (map_T g t) u \<Longrightarrow> P u"
  apply (induction t arbitrary: u g rule: T.induct)
  apply (rule IH)
  apply (auto simp only: map_T_simps True_implies_equals F_rel_map supp_comp_bound bij_comp
      supp_id_bound bij_id id_o
      elim!: alpha.cases)
  apply (elim subshape.cases UnE; simp only: T.inject; hypsubst_thin)
  subgoal premises prems for x g _ f _ h t a y
    apply (insert prems(3-12))
    apply (drule F_set3_transfer[THEN rel_funD, rotated -1];
        (simp only: bij_comp supp_comp_bound)?)
    apply (drule rel_setD2, assumption)
    apply (erule bexE relcomppE GrpE)+
    apply hypsubst_thin
    apply (erule prems(1)[of _ "inv h o g"])
      apply (auto simp only: bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound T_map_comp
        alpha_bij_eq_inv[of "inv _"] inv_inv_eq elim!: alpha_trans alpha_sym)
    done
  subgoal premises prems for x g _ f _ h t a y
    apply (insert prems(3-12))
    apply (drule F_set4_transfer[THEN rel_funD, rotated -1];
        (simp only: bij_comp supp_comp_bound)?)
    apply (drule rel_setD2, assumption)
    apply (erule bexE relcomppE GrpE)+
    apply hypsubst_thin
    apply (erule prems(2)[of _ "inv h o f o g"])
      apply (auto simp only: bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound T_map_comp
        alpha_bij_eq_inv[of "inv _"] inv_inv_eq elim!: alpha_trans alpha_sym)
    done
  done

lemmas subshape_induct[case_names subsh] =
  subshape_induct_raw[OF _ bij_id supp_id_bound, unfolded T_map_id, OF _ alpha_refl]

lemma refresh:
  fixes x :: "('a::var_TT, 'a, 'a T, 'a T) F" assumes A: "|A::'a set| <o bound(any::'a)"
  shows "\<exists> x'. set2_F x' \<inter> A = {} \<and> alpha (ctor x) (ctor x')"
  apply (insert refresh_set2_F[OF A, of x])
  apply (erule exE conjE)+
  subgoal for f
    apply (rule exI[of _ "map_F id f id (map_T f) x"])
    apply (erule conjI)
    apply (rule alpha[of f]; assumption?)
    apply (simp only: F_rel_map_right_bij bij_id supp_id_bound relcompp_conversep_Grp id_apply
        inv_o_simp1 alpha_refl F.rel_refl)
    done
  done

lemma alpha_fresh_cases:
  "alpha (ctor x) (ctor y) \<Longrightarrow> set2_F x \<inter> A = {} \<Longrightarrow> set2_F y \<inter> A = {} \<Longrightarrow>
  |A| <o |UNIV :: 'a :: var_TT set| \<Longrightarrow>
  (\<And>f :: 'a \<Rightarrow> 'a. |supp f| <o |UNIV :: 'a :: var_TT set| \<Longrightarrow> bij f \<Longrightarrow> id_on (FVarsB x) f \<Longrightarrow>
    imsupp f \<inter> A = {} \<Longrightarrow>
    rel_F id f alpha (\<lambda>s. alpha (map_T f s)) x y \<Longrightarrow> P) \<Longrightarrow>
  P"
  apply (erule alpha.cases)
  subgoal for f x y
    apply (unfold T.inject)
    apply (hypsubst_thin)
    apply (frule avoiding_bij(1)[of f "FVarsB x" "set2_F x" "A"];
        (auto simp only: var_TT_infinite simp_thms Un_bound UNION_bound card_of_FVarsB_bound set2_F_bound)?)
    apply (frule avoiding_bij(2)[of f "FVarsB x" "set2_F x" "A"];
        (auto simp only: var_TT_infinite simp_thms Un_bound UNION_bound card_of_FVarsB_bound set2_F_bound)?)
    apply (frule avoiding_bij(3)[of f "FVarsB x" "set2_F x" "A"];
        (auto simp only: var_TT_infinite simp_thms Un_bound UNION_bound card_of_FVarsB_bound set2_F_bound)?)
    apply (frule avoiding_bij(4)[of f "FVarsB x" "set2_F x" "A"];
        (auto simp only: var_TT_infinite simp_thms Un_bound UNION_bound card_of_FVarsB_bound set2_F_bound)?)
    apply (frule avoiding_bij(5)[of f "FVarsB x" "set2_F x" "A"];
        (auto simp only: var_TT_infinite simp_thms Un_bound UNION_bound card_of_FVarsB_bound set2_F_bound)?)
    apply (drule meta_spec[of _ "avoiding_bij f (FVarsB x) (set2_F x) (A)"])
    apply (drule meta_mp, assumption)
    apply (drule meta_mp, assumption)
    apply (drule meta_mp, assumption)
    apply (drule meta_mp) apply blast
    apply (erule meta_mp)
    apply (frule F_set2_transfer[THEN rel_funD, rotated -1];
        (simp only: supp_id_bound)?)
    apply (erule F_rel_mono_strong0[rotated 6];
        auto simp only: supp_id_bound Grp_def)
     apply (rule sym)
     apply (drule spec, erule mp, auto) []
    apply (erule alpha_trans[rotated])
    apply (rule alpha_bij[OF alpha_refl]; assumption?)
    apply (rule ballI)
    subgoal for _ _ z
      apply (cases "z \<in> set2_F x")
       apply (auto simp only: id_on_def dest!: spec[of _ z])
      done
    done
  done

(* destruct avoiding a set: *)
definition avoid :: "('a::var_TT, 'a, 'a T, 'a T) F \<Rightarrow> 'a set \<Rightarrow> ('a::var_TT, 'a, 'a T, 'a T) F" where
  "avoid x A \<equiv> 
  (if set2_F x \<inter> A = {} then x else (SOME x'. set2_F x' \<inter> A = {} \<and> alpha (ctor x) (ctor x')))"

lemma avoid:
  fixes x :: "('a::var_TT, 'a, 'a T, 'a T) F"
  assumes A: "|A| <o bound(any::'a)"  
  shows avoid_fresh: "set2_F (avoid x A) \<inter> A = {}" and alpha_avoid: "alpha (ctor x) (ctor (avoid x A))"
  using someI_ex[OF refresh[OF A, of x]] unfolding avoid_def
  by (auto simp only: alpha_refl split: if_splits)

lemma avoid_triv:
  fixes x :: "('a::var_TT, 'a, 'a T, 'a T) F"
  shows "set2_F x \<inter> A = {} \<Longrightarrow> avoid x A = x"
  by (auto simp only: avoid_def split: if_splits)

lemma supp_asSS_bound:
  "|supp (asSS f::'a::var_TT\<Rightarrow>'a)| <o bound(any::'a)"
  unfolding asSS_def using card_of_empty1 bound_Card_order by (auto simp: supp_id_bound)

lemma alpha_subshape:
  "alpha x y \<Longrightarrow> subshape tt x \<Longrightarrow> subshape tt y"
  apply (erule alpha.cases subshape.cases)+
  apply hypsubst_thin
  apply (unfold T.inject)
  apply hypsubst_thin
  subgoal for f _ y u _ _ x g a b
    apply (erule UnE)
     apply (drule F_set3_transfer[THEN rel_funD, rotated -1]; (simp only: supp_id_bound)?)
     apply (drule rel_setD1, assumption)
     apply (erule bexE conjE)+
     apply (rule subshape.intros[of "u", OF _ _ _ UnI1]; simp)
     apply (erule alpha_trans[rotated])
     apply (rule alpha[of g]; assumption)
    apply (drule F_set4_transfer[THEN rel_funD, rotated -1]; (simp only: supp_id_bound)?)
    apply (drule rel_setD1, assumption)
    apply (erule bexE conjE)+
    apply (rule subshape.intros[of "f o u", OF _ _ _ UnI2]; simp add: supp_comp_bound T_map_comp)
    apply (erule alpha_trans[rotated])
    apply (rule alpha_bij; simp?)
    apply (rule alpha[of "g"]; simp?)
    done
  done

lemma subshape_avoid:
  fixes x :: "('a::var_TT, 'a, 'a T, 'a T)F"
  assumes "|A| <o  bound(any::'a)" 
  shows "subshape tt (ctor (avoid x A)) \<longleftrightarrow> subshape tt (ctor x)"
  apply (rule iffI)
   apply (erule alpha_subshape[OF alpha_sym[OF alpha_avoid[OF assms]]])
  apply (erule alpha_subshape[OF alpha_avoid[OF assms]])
  done

abbreviation cl :: "('a::var_TT T \<Rightarrow> 'a T \<Rightarrow> bool) \<Rightarrow> 'a T \<Rightarrow> 'a T \<Rightarrow> bool" where
  "cl X x y \<equiv>
      (\<exists>g. |supp g| <o bound(any::'a) \<and>  bij g \<and> X (map_T g x) (map_T g y)) \<or> alpha x y"

lemma alpha_coinduct_upto[case_names C]:
  "X x1 x2 \<Longrightarrow>
    (\<And>x1 x2. X x1 x2 \<Longrightarrow>
              \<exists>(f :: 'a::var_TT \<Rightarrow> 'a) x y. x1 = ctor x \<and>
                      x2 = ctor y \<and>
                      |supp f| <o bound(any::'a) \<and>
                      bij f \<and>
                      id_on (FVarsB x) f \<and>
                      rel_F id f (cl X) (\<lambda>s s'. cl X (map_T f s) s') x y) \<Longrightarrow>
    alpha x1 x2"
  apply (rule alpha.coinduct[of "cl X"])
   apply (rule disjI1)
   apply (rule exI[of _ id])
   apply (simp only: bij_id supp_id_bound simp_thms T_map_id)
  apply (erule thin_rl)
  apply (erule disjE exE conjE)+
   apply (drule meta_spec2, drule meta_mp, assumption)
   apply (erule exE conjE)+
  subgoal for l r g f x y
    apply (cases l; cases r)
    apply (auto simp only: map_T_simps T.inject ex_simps simp_thms F_rel_map bij_id supp_id_bound
        o_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound inv_o_simp1 id_on_def o_apply
        F_set_map UN_simps FVars_map_T inv_simp1
        intro!: exI[of _ "inv g \<circ> f \<circ> g"])
    subgoal for _ _ a
      apply (drule spec[of _ "g a"])
      apply (auto simp only: inv_simp1 bij_implies_inject)
      done
    subgoal
      apply (erule F_rel_mono_strong0[rotated 6]; (auto simp only: supp_id_bound
            alpha_bij_eq alpha_bij_eq_inv[of "inv g"] inv_inv_eq
            bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound Grp_def T_map_comp)?)
      subgoal for _ _ h
        apply (auto simp only: bij_comp supp_comp_bound T_map_comp intro!: exI[of _ "h o g"])
        done
      subgoal for _ _ h
        apply (auto simp only: bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound
            T_map_comp[symmetric] o_assoc rewriteR_comp_comp[OF inv_o_simp2] o_id intro!: exI[of _ "h o g"])
        done
      done
    done
  apply (erule thin_rl)
  apply (erule alpha.cases)
  subgoal for _ _ f x y
    apply (rule exI[of _ f])
    apply (auto simp only: supp_id_bound T.inject ex_simps simp_thms
        elim!: F_rel_mono_strong0[rotated 6])
    done
  done


(*********************************)
(* Quotienting *)
(*********************************)

quotient_type 'a TT = "'a::var_TT T" / alpha
  unfolding equivp_def fun_eq_iff using alpha_sym alpha_trans alpha_refl by blast

lemma Quotient_F[quot_map]:
  "Quotient R Abs Rep T \<Longrightarrow> Quotient R' Abs' Rep' T' \<Longrightarrow>
   Quotient (rel_F_id R R') (map_F id id Abs Abs') (map_F id id Rep Rep') (rel_F_id T T')"
  unfolding Quotient_alt_def5 unfolding rel_F_id_def
  unfolding F.rel_conversep[symmetric]
  unfolding F_rel_Grp[OF supp_id_bound bij_id supp_id_bound, symmetric]
  unfolding F.rel_compp[symmetric]
  by (auto elim!: F.rel_mono_strong)

(* Lifted concepts, from terms to tterms: *)

lift_definition cctor :: "('a::var_TT, 'a, 'a TT,'a TT) F \<Rightarrow> 'a TT" is ctor
  apply (rule alpha[of id])
     apply (unfold rel_F_id_def)
     apply (simp_all only: supp_id_bound bij_id id_on_id T_map_id)
  done

lemma abs_TT_ctor: "abs_TT (ctor x) = cctor (map_F id id abs_TT abs_TT x)"
  unfolding cctor_def map_fun_def o_apply unfolding F.map_comp
  unfolding TT.abs_eq_iff
  apply (rule alpha[of id])
     apply (auto simp only: F.rel_map Grp_def supp_id_bound T_map_id o_apply
      alpha_sym[OF Quotient3_rep_abs[OF Quotient3_TT alpha_refl]]
      intro!: F.rel_refl)
  done

lift_definition map_TT :: "('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a TT \<Rightarrow> 'a TT"
  is "map_T o asSS o asBij"
  by (auto simp: alpha_bij_eq asBij_def asSS_def supp_id_bound)

declare F.map_transfer[folded rel_F_id_def, transfer_rule]
declare map_F_transfer[folded rel_F_id_def, transfer_rule]

lemma map_TT_cctor:
  fixes f :: "'a::var_TT \<Rightarrow> 'a"
  assumes "bij f" and "|supp f| <o bound(any::'a)"
  shows "map_TT f (cctor x) = cctor (map_F f f (map_TT f) (map_TT f) x)"
  supply eq_onp_same_args[THEN iffD2, of "\<lambda>f. bij f \<and> |supp f| <o bound(any::'a)", OF conjI[OF assms], transfer_rule]
  supply eq_onp_same_args[THEN iffD2, of "\<lambda>f. |supp f| <o bound(any::'a)", OF assms(2), transfer_rule]
  apply (transfer_start fixing: f)
               defer
               apply transfer_step
              defer
              apply transfer_step
             defer
             defer
             apply transfer_step
            apply transfer_step
           apply transfer_step
          defer
          apply transfer_step
         apply transfer_step
        apply transfer_step
       defer
       apply transfer_step
      apply transfer_step
     apply transfer_step
    apply transfer_step
   apply transfer_step
  apply transfer_end
  apply (auto simp only: o_apply assms asBij_def asSS_def if_True map_T_simps alpha_refl)
  done


lift_definition FFVars :: "'a::var_TT TT \<Rightarrow> 'a set" is FVars
  by (simp add: alpha_FVars)

lemma abs_rep_TT: "abs_TT \<circ> rep_TT = id" 
  apply(rule ext)  
  by simp (meson Quotient3_TT Quotient3_def)

lemma abs_rep_TT2: "abs_TT (rep_TT t) = t"  
  by (simp add: abs_rep_TT comp_eq_dest_lhs)

lemma alpha_rep_abs_TT: "alpha (rep_TT (abs_TT t)) t" 
  using TT.abs_eq_iff abs_rep_TT2 by blast

lemma alpha_ctor_rep_TT_abs_TT: 
"alpha (ctor (map_F id id (rep_TT \<circ> abs_TT) (rep_TT \<circ> abs_TT) x)) (ctor x)"
by (auto intro!: alpha.intros[of id] F.rel_refl_strong 
         simp: supp_id_bound F_rel_map Grp_def OO_def T_map_id  alpha_rep_abs_TT)

lemma card_of_FFVars_bound: "|FFVars t| <o bound(any::'a::var_TT)"
  apply transfer
  apply (rule card_of_FVars_bound)
  done

lemma TT_nchotomy: "\<forall>TT. \<exists>x. TT = cctor x"
  apply transfer
  apply (rule allI)
  subgoal for t by (cases t) (auto simp only: intro: alpha_refl)
  done

lemma FFVars_simps:
  "FFVars (cctor x) =
   set1_F x \<union> (\<Union>t'\<in>set3_F x. FFVars t') \<union> ((\<Union>t'\<in>set4_F x. FFVars t') - set2_F x)"
  apply transfer
  apply (rule FVars_ctor)
  done

lemma FFVars_intros[rule_format]:
  "\<forall>a \<in> set1_F t. a \<in> FFVars (cctor t)"
  "\<forall>t' \<in> set3_F t. \<forall>a \<in> FFVars t'. a \<in> FFVars (cctor t)"
  "\<forall>t' \<in> set4_F t. \<forall>a \<in> FFVars t' - set2_F t. a \<in> FFVars (cctor t)"
    apply (transfer; auto intro: FVars_intros)+
  done

lemma FFVars_cases:
  "a \<in> FFVars (cctor t) \<Longrightarrow>
  (\<forall>a \<in> set1_F t. P) \<Longrightarrow>
  (\<forall>t' \<in> set3_F t. \<forall>a \<in> FFVars t'. P) \<Longrightarrow>
  (\<forall>t' \<in> set4_F t. \<forall>a \<in> FFVars t' - set2_F t. P) \<Longrightarrow>
  P"
  by transfer (auto elim: FVars_cases)

lemma FFVars_induct:
  "a \<in> FFVars (cctor t) \<Longrightarrow>
  (\<And>t. \<forall>a \<in> set1_F t. P a (cctor t)) \<Longrightarrow>
  (\<And>t. \<forall>t' \<in> set3_F t. \<forall>a \<in> FFVars t'. P a t' \<longrightarrow> P a (cctor t)) \<Longrightarrow>
  (\<And>t. \<forall>t' \<in> set4_F t. \<forall>a \<in> FFVars t'.  a \<notin> set2_F t \<longrightarrow> P a t' \<longrightarrow> P a (cctor t)) \<Longrightarrow>
  P a (cctor t)"
  apply transfer
  apply (erule FVars_induct)
    apply simp_all
  done

(* Nonstandard transfer (sensitive to bindings) *)

(* Useful for fresh structural induction and fresh cases: *)
theorem fresh_nchotomy:
  fixes  t :: "('a::var_TT) TT" assumes A: "|A::'a set| <o bound(any::'a)"
  shows
    "\<exists> x. t = cctor x \<and> set2_F x \<inter> A = {}"
  using assms apply transfer
  subgoal for A t by (cases t; auto dest: alpha_avoid avoid_fresh)
  done

theorem fresh_cases:
  fixes  t :: "('a::var_TT) TT" assumes A: "|A::'a set| <o bound(any::'a)"
  obtains x where "t = cctor x" and "set2_F x \<inter> A = {}"
  using fresh_nchotomy[OF assms, of t] by auto

(* This should _not_ be declared as a simp rule, since, thanks
to fresh induction, we will often use plain equality for x and x'
to deduce ctor x = ctor x' *)
theorem TT_inject0:
  fixes x x' :: "('a::var_TT, 'a, 'a TT,'a TT) F"
  shows "cctor x = cctor x' \<longleftrightarrow>
   (\<exists>f. bij f \<and> |supp f| <o bound(any :: 'a) \<and> id_on ((\<Union>t \<in> set4_F x. FFVars t)- set2_F x) f \<and>
        map_F id f id (map_TT f) x = x')"
  apply (simp only: F.rel_eq[symmetric] F_rel_map bij_id supp_id_bound id_o o_id o_apply
      Grp_def id_apply UNIV_I simp_thms OO_eq id_on_def cctor_def map_fun_def TT.abs_eq_iff
      cong: conj_cong)
  apply (safe elim!: alpha.cases)
  subgoal for f
    apply (rule exI[of _ f])
    apply (auto 3 0 simp only: F_rel_map F_set_map id_on_def FFVars_def supp_id_bound bij_id
        Quotient3_rel_rep[OF Quotient3_TT] map_TT_def asBij_def asSS_def Grp_def alpha_refl
        map_fun_def o_id inv_id id_o o_apply id_apply if_True image_id Diff_iff UN_iff
        elim!: F_rel_mono_strong0[rotated 6] alpha_sym[OF alpha_trans[rotated]]
        intro!: trans[OF Quotient3_abs_rep[OF Quotient3_TT, symmetric], OF TT.abs_eq_iff[THEN iffD2]])
    done
  subgoal for f
    apply (rule alpha[of f])
       apply (auto 3 0 simp only: F_rel_map F_set_map id_on_def FFVars_def supp_id_bound bij_id
        map_fun_def o_id inv_id id_o o_apply id_apply if_True image_id Diff_iff UN_iff asBij_def asSS_def
        relcompp_apply conversep_iff UNIV_I simp_thms Grp_def conj_commute[of _ "_ = _"]
        Quotient3_rel_rep[OF Quotient3_TT] map_TT_def alpha_refl
        elim!: F_rel_mono_strong0[rotated 6]
        intro!: Quotient.rep_abs_rsp[OF Quotient3_TT])
    done
  done
 
theorem TT_existential_induct[case_names cctor, consumes 1]:
  fixes t:: "'a::var_TT TT"
  assumes i:
    "\<And> (x::('a, 'a, 'a TT, 'a TT)F).
    \<exists> x'. cctor x' = cctor x \<and>  
         ((\<forall> t \<rho>. t \<in> set3_F x' \<longrightarrow> \<phi> t) \<and> (\<forall> t \<rho>. t \<in> set4_F x'  \<longrightarrow> \<phi> t) 
          \<longrightarrow>   
          \<phi> (cctor x'))"
  shows "\<phi> t"
proof-
  define tt where "tt = rep_TT t"
  {have "\<phi> (abs_TT tt)"
    proof(induct tt rule: subshape_induct)
      case (subsh t)
      obtain x0 where t: "t = ctor x0" by (cases t)
      define xx0 where "xx0 = map_F id id abs_TT abs_TT x0"
      obtain xx where c_xx: "cctor xx = cctor xx0" and 
      imp: "(\<forall>t. t \<in> set3_F xx \<longrightarrow> \<phi> t) \<Longrightarrow> (\<forall>t. t \<in> set4_F xx  \<longrightarrow> \<phi> t) \<Longrightarrow> \<phi> (cctor xx)" 
      using i[of xx0] by blast 
      define x where "x \<equiv> map_F id id rep_TT rep_TT xx"      
      have al: "alpha t (ctor x)" unfolding t using c_xx[symmetric]
        unfolding cctor_def apply auto unfolding xx0_def x_def 
        apply(auto simp: F_map_comp[symmetric] supp_id_bound TT.abs_eq_iff)
        using alpha_ctor_rep_TT_abs_TT[of x0] alpha_trans alpha_sym by blast
      have sht: "\<And> tt. subshape tt t = subshape tt (ctor x)"
        using al alpha_subshape alpha_sym by blast
      have xx: "xx = map_F id id abs_TT abs_TT x" unfolding x_def 
        by (simp add: F_map_comp[symmetric] F_map_id supp_id_bound abs_rep_TT)
      have 0: "abs_TT t = abs_TT (ctor x)" using al by (simp add: TT.abs_eq_iff )
      show ?case unfolding 0 abs_TT_ctor apply(rule imp[unfolded xx])
      by (auto simp: F_set_map supp_id_bound T_map_id sht
              intro!: subsh subshape.intros[OF bij_id supp_id_bound alpha_refl])   
    qed
  }
  thus ?thesis unfolding tt_def abs_rep_TT2 .
qed

theorem TT_fresh_induct_param[case_names cctor, consumes 1]:
  fixes t:: "'a::var_TT TT"
    and Param :: "'param set" and varsOf :: "'param \<Rightarrow> 'a set"
  assumes param: "\<And> \<rho>. \<rho> \<in> Param \<Longrightarrow> |varsOf \<rho> ::'a set| <o bound(any::'a)"
    and i:
    "\<And> (x::('a, 'a, 'a TT, 'a TT)F) \<rho>.
    (* induction hypothesis: *)
    \<lbrakk>\<And>t \<rho>. \<lbrakk>t \<in> set3_F x; \<rho> \<in> Param\<rbrakk> \<Longrightarrow> \<phi> t \<rho>;
     \<And>t \<rho>. \<lbrakk>t \<in> set4_F x; \<rho> \<in> Param\<rbrakk> \<Longrightarrow> \<phi> t \<rho>;
    (* freshness assumption for the parameters: *)
     \<And>a. \<lbrakk>a \<in> set2_F x\<rbrakk> \<Longrightarrow> a \<notin> varsOf \<rho>;
    (* the next two are the <no clash> option: *)
     \<And>a. \<lbrakk>a \<in> set2_F x\<rbrakk> \<Longrightarrow> a \<notin> set1_F x;
     \<And>a t. \<lbrakk>a \<in> set2_F x; t \<in> set3_F x\<rbrakk> \<Longrightarrow> a \<notin> FFVars t;
    \<rho> \<in> Param\<rbrakk>
    \<Longrightarrow>
    \<phi> (cctor x) \<rho>"
  shows "\<forall> \<rho> \<in> Param. \<phi> t \<rho>"  
proof-
  define tt where "tt = rep_TT t"
  {fix \<rho> have "\<rho> \<in> Param \<Longrightarrow> \<phi> (abs_TT tt) \<rho>"
    proof(induct tt arbitrary: \<rho> rule: subshape_induct)
      case (subsh t)
      obtain x0 where x0: "t = ctor x0" by (cases t)
      define x where x: "x \<equiv> avoid x0 (varsOf \<rho> \<union> set1_F x0 \<union> UNION (set3_F x0) FVars)"
      define xx where xx: "xx = map_F id id abs_TT abs_TT x"
      have al: "alpha t (ctor x)"
        unfolding x x0
        by (rule alpha_avoid) (simp only: Un_bound UNION_bound param[OF `\<rho>\<in>Param`] set1_F_bound set3_F_bound card_of_FVars_bound)
      have sht: "\<And> tt. subshape tt t = subshape tt (ctor x)"
        unfolding x x0
        by (rule subshape_avoid[symmetric])
          (simp only: Un_bound UNION_bound param[OF `\<rho>\<in>Param`] set1_F_bound set3_F_bound card_of_FVars_bound)
      have 0: "abs_TT t = abs_TT (ctor x)" using al by (simp add: TT.abs_eq_iff)
      show ?case unfolding 0 abs_TT_ctor using avoid_fresh[of "varsOf \<rho> \<union> set1_F x0 \<union> UNION (set3_F x0) FVars" x0]
        apply (auto 0 3 simp only: F_set_map bij_id supp_id_bound id_apply x sht T_map_id
            Un_bound UNION_bound param[OF `\<rho>\<in>Param`] set1_F_bound set3_F_bound card_of_FVars_bound
            True_implies_equals
            intro!: i subsh subshape.intros[OF bij_id supp_id_bound alpha_refl])
        subgoal for a
          using al
          apply (rule alpha.cases)
          apply (drule rel_funD[OF F_set_transfer(1), rotated -1])
             apply (auto simp only:  image_id eq_alt[symmetric] supp_id_bound x0 x)
          done
        subgoal for a
          using al
          apply (rule alpha.cases)
          apply (drule rel_funD[OF F_set_transfer(3), rotated -1])
             apply (auto 0 3 simp only: image_id eq_alt[symmetric] supp_id_bound x0 x FFVars_def map_fun_def o_apply id_apply
              alpha_FVars[OF Quotient3_rep_abs[OF Quotient3_TT alpha_refl]]
              dest!: alpha_FVars  rel_setD2)
          done
        done
    qed
  }
  thus ?thesis unfolding tt_def
    by (metis Quotient3_TT Quotient3_def)
qed

(* The most useful version of fresh induction: lighter one,
for fixed parameters: *)

lemmas TT_fresh_induct = TT_fresh_induct_param[of UNIV "\<lambda>\<rho>. A" "\<lambda>x \<rho>. P x" for A P, 
   simplified, case_names cctor, consumes 1, induct type]


lemmas TT_plain_induct = TT_fresh_induct[OF emp_bound, simplified, case_names cctor]


theorem map_TT_id: "map_TT id = id"
  apply (rule ext)
  apply transfer
  apply (auto simp only: o_apply asBij_def asSS_def bij_id supp_id_bound if_True T_map_id id_apply alpha_refl)
  done

(* A particular case of vvsubst_cong (for identity) with map_TT instead pf vvsubst *)
lemma map_TT_cong_id: 
  fixes f::"'a::var_TT \<Rightarrow> 'a" 
  assumes "bij f" and "|supp f| <o bound(any::'a)"
    and "\<And>a. a \<in> FFVars t \<Longrightarrow> f a = a" 
  shows "map_TT f t = t"
  using assms(3)
  apply (induct t rule: TT_fresh_induct[consumes 0, of "supp f"])
  apply (simp only: imsupp_supp_bound assms)
  apply (fastforce simp only: map_TT_cctor assms(1,2) TT_inject0 F_map_comp[symmetric] supp_id_bound bij_id
    id_o map_TT_id id_apply FFVars_simps Un_iff UN_iff Diff_iff not_in_supp_alt
    intro!: exI[of _ id] trans[OF F_map_cong F.map_id])
  done

(* One direction of TT_inject with map_TT instead pf vvsubst *)
lemma cctor_eq_intro_map_TT: 
  fixes f :: "'a::var_TT\<Rightarrow>'a"
  assumes "bij f" "|supp f| <o bound(any::'a)"
    and "id_on ((\<Union>t\<in>set4_F x. FFVars t) - set2_F x) f" and "map_F id f id (map_TT f) x = x'"
  shows "cctor x = cctor x'"
  unfolding TT_inject0
  by (rule exI[of _ f] conjI assms)+

end
