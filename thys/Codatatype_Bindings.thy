theory Codatatype_Bindings
  imports Common_Data_Codata_Bindings
begin

(* The type T of pre-terms: In ('a, 'a, 'a T, 'a T) F:
-- the first component 'a represents the free variables
-- the second component 'a represents the binding variables
-- the third (recursive) component of 'a T is free, i.e., not bound by the second component
-- the fourth (recursive) component 'a T is bound by the second component
*)

codatatype 'a::vvar_TT T = ctor "('a, 'a, 'a T, 'a T) F"

(* T acts like a BNF on bijections; but the BNF package did not infer this,
since P is not a BNF; so we need to do the constructions ourselves: *)

definition map_T :: "('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'a T \<Rightarrow> 'a T" where
  "map_T u \<equiv> corec_T (map_F u u Inr Inr o un_ctor)"

lemma map_T_simps:
  fixes u::"'a::vvar_TT\<Rightarrow>'a" assumes u: "bij u" "|supp u| <o bound(any::'a)"
  shows "map_T u (ctor x) = ctor (map_F u u (map_T u) (map_T u) x)"
  unfolding map_T_def apply(rule trans[OF T.corec])
  unfolding map_T_def[symmetric] id_def[symmetric]
  apply (auto simp only: F_map_comp[symmetric] bij_id supp_id_bound u
     o_apply id_o case_sum_o_inj T.sel)
  done

lemma T_map_id: "map_T id t = t"
  apply (coinduction arbitrary: t)
  subgoal for t
    apply (cases t)
    apply
      (auto simp only: map_T_simps bij_id id_apply supp_id_bound T.sel F_rel_map
        id_o Grp_def intro!: F.rel_refl)
    done
  done

lemma T_map_comp:
  fixes u::"'a::vvar_TT\<Rightarrow>'a" and v::"'a::vvar_TT\<Rightarrow>'a"
  assumes u: "bij u" "|supp u| <o bound(any::'a)" and v: "bij v" "|supp v| <o bound(any::'a)"
  shows "map_T (v o u) t = map_T v (map_T u t)"
  apply (coinduction arbitrary: t)
  subgoal for t
    apply (cases t)
    apply (auto simp only: map_T_simps assms F_rel_map T.sel o_id
      bij_comp supp_comp_bound bij_id supp_id_bound bij_imp_bij_inv supp_inv_bound
      o_assoc rewriteR_comp_comp[OF inv_o_simp1] inv_o_simp1 Grp_def
      intro!: F.rel_refl)
    done
  done

inductive free :: "'a::vvar_TT \<Rightarrow> 'a T \<Rightarrow> bool" where
  set1:      "a \<in> set1_F x \<Longrightarrow> free a (ctor x)"
| set2_free: "t \<in> set3_F x \<Longrightarrow> free a t \<Longrightarrow> free a (ctor x)"
| set2_rec:  "t \<in> set4_F x \<Longrightarrow> a \<notin> set2_F x \<Longrightarrow> free a t \<Longrightarrow> free a (ctor x)"

(* Note: free was just an auxiliary -- we will only use FVars *)
definition FVars :: "'a::vvar_TT T \<Rightarrow> 'a set" where
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
  fixes u::"'a::vvar_TT\<Rightarrow>'a" assumes u: "bij u" "|supp u| <o bound(any::'a)"
  shows "a \<in> FVars t \<Longrightarrow> u a \<in> FVars (map_T u t)"
  apply (induct a t rule: FVars_induct)
  subgoal by (auto simp: assms map_T_simps F_set_map intro!: FVars_intros(1))
  subgoal by (auto simp: assms map_T_simps F_set_map intro!: FVars_intros(2))
  subgoal by (auto simp: assms map_T_simps F_set_map intro!: FVars_intros(3))
  done

lemma FVars_map_T:
  fixes u::"'a::vvar_TT\<Rightarrow>'a" assumes u: "bij u" "|supp u| <o bound(any::'a)"
  shows "FVars (map_T u t) = u ` FVars t"
    (*
  apply (induct t rule: T.induct)
  apply (auto 0 5 simp only: FVars_ctor map_T_simps u F_set_map
    image_iff Un_iff UN_iff Diff_iff de_Morgan_conj de_Morgan_disj bex_simps ball_simps
    bex_triv_one_point1 bex_triv_one_point2 bij_implies_inject[OF u(1)])
*)
  apply (rule set_eqI iffI)+
   apply (drule FVars_map_T_le[OF bij_imp_bij_inv[OF u(1)] supp_inv_bound[OF u]];
      (simp only: T_map_comp[symmetric] supp_inv_bound bij_imp_bij_inv inv_o_simp1
        simp_thms T_map_id u inv_simp2 | erule image_eqI[rotated])+)
  apply (erule imageE, drule FVars_map_T_le[OF u], simp only:)
  done

(* Getting enough variables  *)

primrec set_T_level where
  "set_T_level 0 t = {}"
| "set_T_level (Suc n) t = (case t of ctor u \<Rightarrow>
     set1_F u \<union> (\<Union>t \<in> set3_F u. set_T_level n t)
              \<union> (\<Union>t \<in> set4_F u. set_T_level n t))"

lemma set_T_level_bound: "|set_T_level n t| <o bound(any::'a::vvar_TT)"
  apply (induct n arbitrary: t)
   apply (auto intro!: Un_bound UNION_bound F_set2_bd set1_F_bound set3_F_bound set4_F_bound
       emp_bound split: T.splits)
  done

lemma FVars_overapprox: "a \<in> FVars t \<Longrightarrow> a \<in> (\<Union>n. set_T_level n t)"
  apply (induct rule: FVars_induct)
    apply auto
    apply (auto intro!: exI[of _ "Suc _"] | (erule bexI[rotated], erule bexI[rotated], assumption))+
  done

lemma card_of_FVars_bound: "|FVars t| <o bound(any::'a::vvar_TT)"
  apply (rule ordLeq_ordLess_trans[OF card_of_mono1[OF subsetI[OF FVars_overapprox]]], assumption)
  apply (rule UNION_bound[of "UNIV :: nat set", OF _ set_T_level_bound])
  using ordLess_Field Field_natLeq natLeq_bound by fastforce
(*
  apply (induct t rule: T.induct)
  subgoal for t
    apply (auto simp only: FVars_ctor
        intro!: Un_bound UNION_bound set1_F_bound set2_F_bound set3_F_bound set4_F_bound
        ordLeq_ordLess_trans[OF card_of_diff])
    done
  done
*)


(* Alpha Equivalence *)

abbreviation "FVarsB x \<equiv> UNION (set4_F x) FVars - set2_F x"

coinductive alpha :: "'a::vvar_TT T \<Rightarrow> 'a T \<Rightarrow> bool"
  where alpha: "|supp f| <o bound(any::'a) \<Longrightarrow> bij f \<Longrightarrow> id_on (FVarsB x) f \<Longrightarrow>
    rel_F id f alpha (\<lambda>s s'. alpha (map_T f s) s') x y \<Longrightarrow> alpha (ctor x) (ctor y)"
    monos F_rel_mono[OF supp_id_bound] conj_context_mono

lemmas alpha_def_from_paper = alpha.intros[unfolded rel_F_def]

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
  fixes u :: "'a::vvar_TT\<Rightarrow> 'a" and v :: "'a::vvar_TT\<Rightarrow> 'a"
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
  fixes u :: "'a::vvar_TT\<Rightarrow> 'a"
  assumes "bij u"  "|supp u| <o bound(any::'a)"
  shows "alpha (map_T u t) (map_T u t') = alpha t t'"
  apply (rule iffI)
   apply (drule alpha_bij[OF _ _ bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms] bij_imp_bij_inv[OF assms(1)] supp_inv_bound[OF assms]];
      auto simp only: assms T_map_comp[symmetric] T_map_id supp_inv_bound bij_imp_bij_inv inv_o_simp1)
  apply (erule alpha_bij[OF _ _ assms assms]; simp)
  done

lemma alpha_bij_eq_inv:
  fixes u :: "'a::vvar_TT\<Rightarrow> 'a"
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
  apply (drule conjunct1)
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
  fixes t :: "('a::vvar_TT) T" and x :: "('a, 'a, 'a T, 'a T) F" assumes A: "|A::'a set| <o bound(any::'a)"
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

lemma refresh:
  fixes x :: "('a::vvar_TT, 'a, 'a T, 'a T) F" assumes A: "|A::'a set| <o bound(any::'a)"
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
  |A| <o |UNIV :: 'a :: vvar_TT set| \<Longrightarrow>
  (\<And>f :: 'a \<Rightarrow> 'a. |supp f| <o |UNIV :: 'a :: vvar_TT set| \<Longrightarrow> bij f \<Longrightarrow> id_on (FVarsB x) f \<Longrightarrow>
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
definition avoid :: "('a::vvar_TT, 'a, 'a T, 'a T) F \<Rightarrow> 'a set \<Rightarrow> ('a::vvar_TT, 'a, 'a T, 'a T) F" where
  "avoid x A \<equiv> (if set2_F x \<inter> A = {} then x else (SOME x'. set2_F x' \<inter> A = {} \<and> alpha (ctor x) (ctor x')))"

lemma avoid:
  fixes x :: "('a::vvar_TT, 'a, 'a T, 'a T) F"
  assumes A: "|A| <o bound(any::'a)"  
  shows avoid_fresh: "set2_F (avoid x A) \<inter> A = {}" and alpha_avoid: "alpha (ctor x) (ctor (avoid x A))"
  using someI_ex[OF refresh[OF A, of x]] unfolding avoid_def
  by (auto simp only: alpha_refl split: if_splits)

lemma avoid_triv:
  fixes x :: "('a::vvar_TT, 'a, 'a T, 'a T) F"
  shows "set2_F x \<inter> A = {} \<Longrightarrow> avoid x A = x"
  by (auto simp only: avoid_def split: if_splits)

abbreviation cl :: "('a :: vvar_TT T \<Rightarrow> 'a T \<Rightarrow> bool) \<Rightarrow> 'a T \<Rightarrow> 'a T \<Rightarrow> bool" where
  "cl X x y \<equiv>
      (\<exists>g. |supp g| <o bound(any::'a) \<and>  bij g \<and> X (map_T g x) (map_T g y)) \<or> alpha x y"

lemma alpha_coinduct_upto[case_names C]:
  "X x1 x2 \<Longrightarrow>
    (\<And>x1 x2. X x1 x2 \<Longrightarrow>
              \<exists>(f :: 'a::vvar_TT \<Rightarrow> 'a) x y. x1 = ctor x \<and>
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

quotient_type 'a TT = "'a::vvar_TT T" / alpha
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

lift_definition cctor :: "('a::vvar_TT, 'a, 'a TT,'a TT) F \<Rightarrow> 'a TT" is ctor
  apply (rule alpha[of id])
     apply (unfold rel_F_id_def)
     apply (simp_all only: supp_id_bound bij_id id_on_id T_map_id)
  done

lift_definition map_TT :: "('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'a TT \<Rightarrow> 'a TT"
  is "map_T o asSS o asBij"
  by (auto simp: alpha_bij_eq asBij_def asSS_def supp_id_bound)

declare F.map_transfer[folded rel_F_id_def, transfer_rule]
declare map_F_transfer[folded rel_F_id_def, transfer_rule]

lemma map_TT_cctor:
  fixes f :: "'a::vvar_TT \<Rightarrow> 'a"
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

lift_definition FFVars :: "'a::vvar_TT TT \<Rightarrow> 'a set" is FVars
  by (simp add: alpha_FVars)

lemma card_of_FFVars_bound: "|FFVars t| <o bound(any::'a::vvar_TT)"
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
  "a \<in> FFVars t \<Longrightarrow>
  (\<And>t. \<forall>a \<in> set1_F t. P a (cctor t)) \<Longrightarrow>
  (\<And>t. \<forall>t' \<in> set3_F t. \<forall>a \<in> FFVars t'. P a t' \<longrightarrow> P a (cctor t)) \<Longrightarrow>
  (\<And>t. \<forall>t' \<in> set4_F t. \<forall>a \<in> FFVars t'.  a \<notin> set2_F t \<longrightarrow> P a t' \<longrightarrow> P a (cctor t)) \<Longrightarrow>
  P a t"
  apply transfer
  apply (erule FVars_induct)
    apply simp_all
  done

(* Nonstandard transfer (sensitive to bindings) *)

(* Useful for fresh structural induction and fresh cases: *)
theorem fresh_nchotomy:
  fixes  t :: "('a::vvar_TT) TT" assumes A: "|A::'a set| <o bound(any::'a)"
  shows
    "\<exists> x. t = cctor x \<and> set2_F x \<inter> A = {}"
  using assms apply transfer
  subgoal for A t by (cases t; auto dest: alpha_avoid avoid_fresh)
  done

theorem fresh_cases:
  fixes  t :: "('a::vvar_TT) TT" assumes A: "|A::'a set| <o bound(any::'a)"
  obtains x where "t = cctor x" and "set2_F x \<inter> A = {}"
  using fresh_nchotomy[OF assms, of t] by auto


(* This should _not_ be declared as a simp rule, since, thanks
to fresh induction, we will often use plain equality for x and x'
to deduce ctor x = ctor x' *)
theorem TT_inject0:
  fixes x x' :: "('a::vvar_TT, 'a, 'a TT,'a TT) F"
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

lemma alpha_invariant:
  "Domainp (rel_fun cr_TT (rel_fun cr_TT (=))) R \<Longrightarrow> (alpha OO R OO alpha) x y \<Longrightarrow> R x y"
  by (auto simp only:
    Domainp.simps rel_fun_def cr_TT_def fun_eq_iff TT.abs_eq_iff[symmetric] relcompp_apply)

coinductive alpha2 :: "'a::vvar_TT T \<Rightarrow> 'a T \<Rightarrow> bool"
  where alpha2: "|supp f| <o bound(any::'a) \<Longrightarrow> bij f \<Longrightarrow> id_on (FVarsB x) f \<Longrightarrow>
    |supp g| <o bound(any::'a) \<Longrightarrow> bij g \<Longrightarrow> id_on (FVarsB y) g \<Longrightarrow>
    rel_F id (inv g o f) alpha2 (\<lambda>s s'. alpha2 (map_T f s) (map_T g s')) x y \<Longrightarrow> alpha2 (ctor x) (ctor y)"
    monos F_rel_mono[OF supp_id_bound bij_comp[OF _ bij_imp_bij_inv] supp_comp_bound[OF supp_inv_bound]] conj_context_mono

lemma alpha2_bij_eq_inv:
  fixes u :: "'a::vvar_TT \<Rightarrow> 'a"
  assumes "bij u" "|supp u| <o bound(any::'a)"
  shows "alpha2 (map_T u t1) t2 \<Longrightarrow> alpha2 t1 (map_T (inv u) t2)"
  apply (coinduction arbitrary: t1 t2)
  apply (erule alpha2.cases)
  subgoal for t1 t2 f x g y
    apply (cases t1)
    apply (simp only: T.inject simp_thms ex_simps)
    apply (rule exI[of _ "inv u o f o u"])
    apply (rule exI[of _ "inv u o g o u"])
    apply (auto simp only: assms map_T_simps T.inject simp_thms o_inv_distrib inv_inv_eq o_assoc
      rewriteR_comp_comp[OF inv_o_simp2] inv_o_simp2 inv_simp2
      o_id F_set_map F_rel_map id_on_def o_apply FVars_map_T id_o
      bij_id supp_id_bound bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound
      Grp_def relcompp_apply conversep_iff T_map_comp UNIV_I
      elim!: F_rel_mono_strong0[rotated 6])+
    subgoal for _ a t
      apply (drule spec[of _ "u a"])
      apply (auto simp only: UN_iff bex_simps FVars_map_T assms image_iff bij_implies_inject inv_simp1
        elim!: bexI[rotated])
      done
    subgoal
      apply (rule exI conjI[rotated] refl)+
      apply (rule disjI1 exI conjI refl)+
      apply (simp only: T_map_comp[symmetric] assms bij_imp_bij_inv supp_inv_bound inv_o_simp2 T_map_id)
      done
    done
  done

lemma alpha2_FVars_le:
  "x \<in> FVars t \<Longrightarrow> alpha2 t t' \<Longrightarrow> x \<in> FVars t'"
  apply (induct x t arbitrary: t' rule: FVars_induct; elim alpha2.cases)
    apply (simp_all only: T.inject FVars_ctor)
    apply (rule UnI1, rule UnI1)
    apply (drule rel_funD[OF F_set_transfer(1)[OF supp_id_bound], rotated -1];
      auto simp only: Grp_UNIV_id image_id bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound)
   apply (rule UnI1, rule UnI2)
   apply (drule rel_funD[OF F_set_transfer(3)[OF supp_id_bound], rotated -1];
      auto 0 3 simp only: rel_set_def bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound)
  apply (rule UnI2)
  apply (frule rel_funD[OF F_set_transfer(2)[OF supp_id_bound], rotated -1]; (simp only: Grp_def bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound)?)
  apply (drule conjunct1)
  apply (drule rel_funD[OF F_set_transfer(4)[OF supp_id_bound], rotated -1]; (simp only: rel_set_def  bij_comp supp_comp_bound bij_imp_bij_inv supp_inv_bound)?)
  apply (drule conjunct1)
  apply (drule bspec, assumption, erule bexE)
  apply (drule alpha2_bij_eq_inv[rotated -1]; (simp only: )?)
  apply (drule meta_spec, drule meta_mp, assumption)
  apply (simp only: FVars_map_T bij_imp_bij_inv supp_inv_bound)
  apply (erule imageE)+
  apply hypsubst_thin
  subgoal for t _ _ _ f x g y u _ b
    unfolding id_on_def
    apply (drule spec[of _ "inv f b"])
    apply (drule spec[of _ b])
    apply (drule mp)
    apply (auto simp only: o_apply inv_simp2 inv_simp1) []
    apply (drule mp)
    apply (auto simp only: o_apply inv_simp2 inv_simp1) []
    apply (auto simp only: o_apply id_on_def inv_simp1 inv_simp2 UN_iff elim!: bexI[rotated])
    done
  done

lemma alpha_alpha2: "alpha x y = alpha2 x y"
  apply (rule iffI)
  apply (coinduction arbitrary: x y)
  apply (erule alpha.cases)
  apply (simp only: T.inject ex_simps simp_thms)
  subgoal for _ _ f x y
    apply (rule exI[of _ f])
    apply (auto simp only: supp_id_bound T_map_id inv_id id_o intro!: exI[of _ id]
      elim!: F_rel_mono_strong0[rotated 6])
    done
  apply (coinduction arbitrary: x y rule: alpha_coinduct_upto)
  apply (erule alpha2.cases)
  apply (simp only: T.inject ex_simps simp_thms)
  subgoal for _ _ f x g y
    apply (rule exI[of _ "inv g o f"])
    apply (auto simp only: supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv supp_id_bound
      id_on_def o_apply bij_imp_inv
      elim!: F_rel_mono_strong0[rotated 6])
    subgoal for a t
      apply (frule rel_funD[OF F_set_transfer(2)[OF supp_id_bound], rotated -1]; (simp only: Grp_def bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound)?)
      apply (drule conjunct1)
      apply (drule rel_funD[OF F_set_transfer(4)[OF supp_id_bound], rotated -1]; (simp only: rel_set_def bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound)?)
      apply (drule conjunct1)
      apply (drule bspec, assumption)
      apply (erule bexE)
      apply (drule alpha2_FVars_le[rotated, of _ _ "f a"])
       apply (rule set_mp[OF equalityD2[OF FVars_map_T]]; assumption?)
       apply (erule imageI)
      apply (drule set_mp[OF equalityD1[OF FVars_map_T], rotated 2]; assumption?)
      apply (erule imageE)
      subgoal for u b
        apply (drule spec[of _ a])
        apply (drule spec[of _ b])
        apply (auto simp only: bij_imp_inv o_apply inv_simp2 bij_implies_inject)
        done
      done
    subgoal
      apply (rule exI[of _ id])
      apply (simp only: bij_id supp_id_bound T_map_id)
      done
    subgoal
      apply (rule exI[of _ g])
      apply (simp only: bij_id supp_id_bound T_map_comp[symmetric] o_assoc
        supp_comp_bound supp_inv_bound bij_comp bij_imp_bij_inv inv_o_simp2 id_o)
      done
    done
  done

declare F.rel_transfer[folded rel_F_id_def, transfer_rule]

theorem TT_existential_coinduct: 
  fixes t1 t2 :: "'a::vvar_TT TT" 
  assumes R:"R t1 t2" and
    co: "\<And> (x1::('a, 'a, 'a TT, 'a TT) F) (x2::('a, 'a, 'a TT, 'a TT) F).
    (* Existential assumption for coinduction: *)
    R (cctor x1) (cctor x2) \<Longrightarrow> (\<exists>xx1 xx2. 
    cctor xx1 = cctor x1 \<and> cctor xx2 = cctor x2 \<and> 
    rel_F id id (\<lambda>t1 t2. R t1 t2  \<or> t1 = t2) (\<lambda>t1 t2. R t1 t2 \<or> t1 = t2) xx1 xx2)"
  shows "t1 = t2"
  using assms unfolding rel_F_id_def[symmetric]
  apply transfer
  subgoal premises prems for R t1 t2
    apply (rule alpha_alpha2[THEN iffD2])
    apply (rule alpha2.coinduct[of R, OF prems(2)])
    apply (unfold alpha_alpha2[THEN sym])
    subgoal for x y
      apply (cases x; cases y)
      apply hypsubst_thin
      apply (drule prems(3))
      apply (erule exE conjE)+
      apply (drule alpha_sym)
      apply (drule alpha_sym)
      apply (erule alpha.cases)+
      apply (auto simp only: T.inject simp_thms ex_simps rel_F_id_def)
      subgoal for f l m1 g r m2
      apply (rule exI[of _ f])
        apply (auto simp only: T.inject supp_id_bound bij_id id_on_id simp_thms ex_simps T_map_id elim!: alpha.cases
          intro!: exI[of _ g])
        apply (erule F_rel_mono_strong0[rotated 6, OF F_rel_comp_leq[THEN predicate2D], rotated 6, OF relcomppI])
                        apply (erule F_rel_comp_leq[THEN predicate2D, rotated 6, OF relcomppI])
        apply (erule F_rel_flip[THEN iffD2, rotated 4])
                            apply (rule ballI, rule refl | rule ballI, rule ballI, rule imp_refl | assumption |
            auto simp only: o_id supp_comp_bound supp_id_bound bij_comp bij_id T_map_comp inv_id bij_imp_bij_inv supp_inv_bound)+
        subgoal
          apply (auto simp only: bij_id supp_id_bound T_map_id
            intro!: alpha_invariant[OF prems(1)])
          apply (erule relcomppI)
          apply (erule relcomppI)
          apply (erule alpha_sym)
          done
        subgoal
          apply (erule notE)
          apply (erule alpha_trans)
          apply (erule alpha_trans)
          apply (erule alpha_sym)
          done
        subgoal
          apply (auto simp only: bij_id supp_id_bound T_map_id
            intro!: alpha_invariant[OF prems(1)])
          apply (erule relcomppI)
          apply (erule relcomppI)
          apply (erule alpha_sym)
          done
        subgoal
          apply (erule notE)
          apply (erule alpha_trans)
          apply (erule alpha_trans)
          apply (erule alpha_sym)
          done
        done
      done
    done
  done

theorem TT_fresh_coinduct_param: 
  fixes t1:: "'a::vvar_TT TT" and  t2:: "'a::vvar_TT TT"
    and Param :: "'param set" and varsOf :: "'param \<Rightarrow> 'a set"
  assumes param: "\<And> \<rho>. \<rho> \<in> Param \<Longrightarrow> |varsOf \<rho> ::'a set| <o bound(any::'a)"
    and R:"R t1 t2 \<rho>" and rho:"\<rho> \<in> Param" and
    co: "\<And> (x1::('a, 'a, 'a TT, 'a TT) F) (x2::('a, 'a, 'a TT, 'a TT) F) \<rho>.
    \<lbrakk>(*usual assumption for coinduction*)
    R (cctor x1) (cctor x2) \<rho>;
    (* freshness assumption for the parameters: *)
     \<And>a. a \<in> set2_F x1 \<Longrightarrow> a \<notin> varsOf \<rho>;
     \<And>a. a \<in> set2_F x2 \<Longrightarrow> a \<notin> varsOf \<rho>;
    \<rho> \<in> Param\<rbrakk> 
    \<Longrightarrow>  
    rel_F id id (\<lambda>t1 t2. \<exists> \<rho>. \<rho> \<in> Param \<and> R t1 t2 \<rho> \<or> t1 = t2) (\<lambda>t1 t2. \<exists> \<rho>. \<rho> \<in> Param \<and> R t1 t2 \<rho> \<or> t1 = t2) x1 x2"
  shows "t1 = t2"
  apply (rule TT_existential_coinduct[of "\<lambda> t1 t2. \<exists> \<rho>. \<rho> \<in> Param \<and> R t1 t2 \<rho>"])
   apply ((rule exI conjI R rho)+) []
  apply (erule exE conjE)+
  apply (insert co)
  apply (unfold rel_F_id_def[symmetric])
  subgoal for x y rho
    apply (rule fresh_cases[OF param, of _ "cctor x"], assumption)
    apply (rule fresh_cases[OF param, of _ "cctor y"], assumption)
    apply (rule exI conjI | erule sym)+
    apply fastforce
    done
  done

lemmas TT_fresh_coinduct[case_names cctor, consumes 2] =
  TT_fresh_coinduct_param[of UNIV "\<lambda>\<rho>. A" "\<lambda>l r \<rho>. R l r" for A R, simplified]

lemmas TT_plain_coinduct = TT_fresh_coinduct[OF emp_bound, simplified]

theorem map_TT_id: "map_TT id = id"
  apply (rule ext)
  apply transfer
  apply (auto simp only: o_apply asBij_def asSS_def bij_id supp_id_bound if_True T_map_id id_apply alpha_refl)
  done

(* A particular case of vvsubst_cong (for identity) with map_TT instead pf vvsubst *)
lemma map_TT_cong_id: 
  fixes f::"'a::vvar_TT \<Rightarrow> 'a" 
  assumes "bij f" and "|supp f| <o bound(any::'a)"
    and "\<And>a. a \<in> FFVars t \<Longrightarrow> f a = a" 
  shows "map_TT f t = t"
  using assms(3)
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (rule fresh_cases[of "supp f" t, OF assms(2)])
    apply (simp only: imsupp_supp_bound assms map_TT_cctor)
    apply (rule exI conjI refl)+
    apply (simp only: assms F_rel_map supp_id_bound bij_id id_o)
    apply (rule F_rel_mono_strong0[rotated 6, OF F.rel_eq[THEN predicate2_eqD, THEN iffD2], OF refl])
    apply (auto simp only: supp_id_bound bij_id assms(1,2) o_apply id_apply id_o
      relcompp_apply Grp_def FFVars_simps simp_thms eqTrueI[OF UNIV_I]
      disjoint_eq_subset_Compl subset_eq Compl_iff not_in_supp_alt)
    done
  done

(* One direction of TT_inject with map_TT instead pf vvsubst *)
lemma cctor_eq_intro_map_TT: 
  fixes f :: "'a::vvar_TT\<Rightarrow>'a"
  assumes "bij f" "|supp f| <o bound(any::'a)"
    and "id_on ((\<Union>t\<in>set4_F x. FFVars t) - set2_F x) f" and "map_F id f id (map_TT f) x = x'"
  shows "cctor x = cctor x'"
  unfolding TT_inject0
  by (rule exI[of _ f] conjI assms)+

end
