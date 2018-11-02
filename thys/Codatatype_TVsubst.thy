theory Codatatype_TVsubst
  imports Codatatype_VVsubst
begin

consts \<eta> :: "'a::vvar_TT \<Rightarrow> ('a, 'b, 'c, 'd) F"

axiomatization where
  \<eta>_set1_F: "\<And>a. set1_F (\<eta> a) = {a}"
  and
  \<eta>_inj: "\<And> a1 a2. \<eta> a1 = \<eta> a2 \<Longrightarrow> a1 = a2"
  and
  \<eta>_compl_set1_F: "\<And> x. x \<notin> range \<eta> \<Longrightarrow> set1_F x = {}"
  and
  \<eta>_natural: "\<And> (f::'a::vvar_TT \<Rightarrow> 'a) (g::'b::vvar_TT \<Rightarrow> 'b) h i. |supp f| <o bound(any::'a) \<Longrightarrow> bij g \<Longrightarrow> |supp g| <o bound(any::'b) \<Longrightarrow> map_F f g h i o \<eta> = \<eta> o f"

(* Immediately satisfied if ('a,'b) F has the form 'a + 'b G *)
lemma map_F_\<eta>:
  "|supp f| <o bound(any::'a) \<Longrightarrow> bij g \<Longrightarrow> |supp g| <o bound(any::'b) \<Longrightarrow>
   map_F  (f::'a::vvar_TT \<Rightarrow> 'a) (g::'b::vvar_TT \<Rightarrow> 'b) i j (\<eta> x) = \<eta> (f x)"
  using \<eta>_natural[of f g] unfolding fun_eq_iff by auto

lemma supp_swap_bound: "|supp (id (x := y, y := x :: 'a))| <o bound(any :: 'a :: vvar_TT)"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF supp_swap_le] finite_ordLess_infinite2])
    (auto simp: var_TT_infinite)


lemma \<eta>_set2_F:
  fixes a :: "'a::vvar_TT"
  shows "set2_F (\<eta> a :: ('a :: vvar_TT, 'b :: vvar_TT, 'c, 'd) F) = {}"
proof -
  { fix b :: 'b
    assume "b \<in> set2_F (\<eta> a :: ('a :: vvar_TT, 'b :: vvar_TT, 'c, 'd) F)"
    then have "c \<in> set2_F ((\<eta> o id) a :: ('a :: vvar_TT, 'b :: vvar_TT, 'c, 'd) F)" for c
      by (subst \<eta>_natural[symmetric, of id "id(b:=c,c:=b) :: _ \<Rightarrow> _ :: vvar_TT" id id])
        (auto 0 1 simp only: F_set2_map image_iff supp_id_bound bij_swap supp_swap_bound o_apply
          fun_upd_apply id_apply intro: supp_id_bound supp_swap_bound split: if_splits)
    then have "set2_F (\<eta> a :: ('a :: vvar_TT, 'b :: vvar_TT, 'c, 'd) F) = (UNIV :: 'b set)"
      by auto
    then have False
      by (metis F_set2_bd not_ordLess_ordLeq var_TT)
  }
  then show ?thesis by blast
qed

lemma \<eta>_set3_F:
  fixes a :: "'a::vvar_TT"
  shows "set3_F (\<eta> a :: ('a :: vvar_TT, 'b :: vvar_TT, 'c, 'd) F) = {}"
proof -
  { fix b :: 'c
    assume "b \<in> set3_F (\<eta> a :: ('a :: vvar_TT, 'b :: vvar_TT, 'c, 'd) F)"
    then have "c \<in> set3_F ((\<eta> o id) a :: ('a :: vvar_TT, 'b :: vvar_TT, bd_type_TT set, 'd) F)" for c
      by (subst \<eta>_natural[symmetric, of id "id :: _ \<Rightarrow> _ :: vvar_TT" "\<lambda>_. c" id])
        (auto simp add: F_set3_map image_iff supp_id_bound intro!: supp_id_bound)
    then have *: "set3_F (\<eta> a :: ('a :: vvar_TT, 'b :: vvar_TT, bd_type_TT set, 'd) F) = (UNIV :: bd_type_TT set set)"
      by auto
    have "bd_TT <o |set3_F (\<eta> a :: ('a :: vvar_TT, 'b :: vvar_TT, bd_type_TT set, 'd) F) :: bd_type_TT set set|"
      unfolding * using Card_order_Pow F.bd_card_order card_order_on_Card_order by force
    with F.set_bd[of "\<eta> a"] have False
      using not_ordLeq_ordLess by blast
  }
  then show ?thesis by blast
qed

lemma \<eta>_set4_F:
  fixes a :: "'a::vvar_TT"
  shows "set4_F (\<eta> a :: ('a :: vvar_TT, 'b :: vvar_TT, 'c, 'd) F) = {}"
proof -
  { fix b :: 'd
    assume "b \<in> set4_F (\<eta> a :: ('a :: vvar_TT, 'b :: vvar_TT, 'c, 'd) F)"
    then have "c \<in> set4_F ((\<eta> o id) a :: ('a :: vvar_TT, 'b :: vvar_TT, 'c, bd_type_TT set) F)" for c
      by (subst \<eta>_natural[symmetric, of id "id :: _ \<Rightarrow> _ :: vvar_TT" id "\<lambda>_. c"])
        (auto simp add: F_set4_map image_iff supp_id_bound intro!: supp_id_bound)
    then have *: "set4_F (\<eta> a :: ('a :: vvar_TT, 'b :: vvar_TT, 'c, bd_type_TT set) F) = (UNIV :: bd_type_TT set set)"
      by auto
    have "bd_TT <o |set4_F (\<eta> a :: ('a :: vvar_TT, 'b :: vvar_TT, 'c, bd_type_TT set) F) :: bd_type_TT set set|"
      unfolding * using Card_order_Pow F.bd_card_order card_order_on_Card_order by force
    with F.set_bd[of "\<eta> a"] have False
      using not_ordLeq_ordLess by blast
  }
  then show ?thesis by blast
qed


lemma \<eta>_transfer[folded rel_F_id_def, transfer_rule]:
  "rel_fun (=) (rel_F (id :: 'a::vvar_TT\<Rightarrow>'a) (id :: 'a::vvar_TT\<Rightarrow>'a) R S) \<eta> \<eta>"
  unfolding rel_fun_def F_rel_map_set2[OF supp_id_bound bij_id supp_id_bound]
  apply safe
  subgoal for _ x
    apply (rule exI[of _ "map_F id id _ _ (\<eta> x)"])
    apply (unfold F.set_map F.map_comp)
    apply (subst map_F_\<eta>; auto simp: \<eta>_set3_F \<eta>_set4_F supp_id card_of_empty4)+
    done
  done

definition VVr :: "'a::vvar_TT \<Rightarrow> 'a TT" where "VVr a \<equiv> cctor (\<eta> a)"

lemma VVr_inj: "VVr a1 = VVr a2 \<longleftrightarrow> a1 = a2"
  unfolding VVr_def by (auto simp add: \<eta>_inj TT_inject map_F_\<eta> supp_id_bound)

definition isVVr :: "'a::vvar_TT TT \<Rightarrow> bool" where
  "isVVr t \<equiv> (\<exists>a. t = VVr a)"

definition asVVr :: "'a::vvar_TT TT \<Rightarrow> 'a" where
  "asVVr t \<equiv> if isVVr t then (SOME a. VVr a = t) else undefined"

lemma asVVr_VVr:
  shows "asVVr (VVr t) = t"
  unfolding asVVr_def apply(rule someI_ex)
  unfolding isVVr_def by (auto simp: VVr_inj)

lemma isVVr_asVVr:
  assumes "isVVr t" shows "VVr (asVVr t) = t"
  unfolding asVVr_def apply(rule someI_ex)
  using assms unfolding isVVr_def by (auto simp: VVr_inj)

lemma FFVars_VVr: "FFVars (VVr a) = {a}"
  unfolding VVr_def by (auto simp: \<eta>_set1_F \<eta>_set3_F \<eta>_set4_F FFVars_simps)

lemma isVVr_FFVars_asVVr:
  assumes "isVVr t" shows "FFVars t = {asVVr t}"
  by (metis FFVars_VVr assms isVVr_asVVr)

lemma map_TT_VVr: "bij (g::'a::vvar_TT\<Rightarrow>'a) \<Longrightarrow> |supp g| <o bound(any::'a) \<Longrightarrow> map_TT g (VVr a) = VVr (g a)"
  unfolding VVr_def by (auto simp: \<eta>_natural[unfolded o_def fun_eq_iff, rule_format] map_TT_cctor)

(***************************************)
(* Substitution of terms for variables  *)
(***************************************)

(* The Support of a substitution function f: *)
definition SSupp :: "('a::vvar_TT \<Rightarrow> 'a TT) \<Rightarrow> 'a set" where
  "SSupp f \<equiv> {a . f a \<noteq> VVr a}"

(* The Support of f factoring in the image too: *)
definition IImsupp :: "('a::vvar_TT \<Rightarrow> 'a TT) \<Rightarrow> 'a set" where
  "IImsupp f \<equiv> SSupp f \<union> (\<Union> a \<in> SSupp f. FFVars (f a))"

lemma SSupp_VVr_bound: "|SSupp VVr| <o bound(any::'a::vvar_TT)"
  unfolding SSupp_def by (auto simp: emp_bound)


lemma IImsupp_SSupp_bound:
  "|IImsupp (g::'a::vvar_TT\<Rightarrow>'a TT)| <o bound(any::'a) \<longleftrightarrow> |SSupp g| <o bound(any::'a)"
  apply (rule iffI)
   apply (erule ordLeq_ordLess_trans[rotated])
   apply (rule card_of_mono1)
   apply (auto simp: IImsupp_def) []
  apply (auto simp only: IImsupp_def bound_cinfinite bound_Card_order card_of_FFVars_bound
      intro!: Un_bound UNION_bound)
  done

lemma not_isVVr_set1_F:
  assumes "\<not> isVVr (cctor x)"
  shows "set1_F x = {}"  
  using assms unfolding isVVr_def VVr_def
  by simp (metis \<eta>_compl_set1_F image_iff)

lemma IImsupp_imsupp_map_TT_commute:
  fixes f :: "'a::vvar_TT\<Rightarrow>'a TT" and g :: "'a::vvar_TT\<Rightarrow>'a"
  assumes fg: "IImsupp f \<inter> imsupp g = {}" and gg: "bij g" "|supp g| <o bound(any::'a)"
  shows "map_TT g (f a) = f (g a)"
proof(cases "g a = a")
  case True note g = True
  show ?thesis proof(cases "f a = VVr a")
    case True thus ?thesis using g gg by (simp add: map_TT_VVr)
  next
    case False hence "map_TT g (f a) = f a"
      using fg gg
      by (intro map_TT_cong_id)
        (auto simp:  IImsupp_def SSupp_def imsupp_def supp_def)
    then show ?thesis using g alpha_sym by auto
  qed
next
  case False
  hence f: "f a = VVr a" using fg unfolding imsupp_def supp_def IImsupp_def SSupp_def by auto
  have "g (g a) \<noteq> g a" using gg False unfolding bij_def inj_on_def by auto
  hence "f (g a) = VVr (g a)" using fg unfolding imsupp_def supp_def IImsupp_def SSupp_def by auto
  thus ?thesis using False f gg by (simp add: map_TT_VVr)
qed

theorem TT_VVr_cases[case_names VVr nonVVr, cases type: TT]:
  fixes t :: "'a::vvar_TT TT"
  obtains a where "t = VVr a" | "\<not> isVVr t"
  by (metis isVVr_asVVr)

typedef 'a :: vvar_TT SSfun = "{f :: 'a \<Rightarrow> 'a TT. |SSupp f| <o bound(any :: 'a)}"
  by (auto intro!: exI[of _ VVr] simp: SSupp_VVr_bound)

lemma map_TT_eq_VVr_iff:
  "bij (f :: 'a \<Rightarrow> 'a :: vvar_TT) \<Longrightarrow> |supp f| <o bound(any :: 'a) \<Longrightarrow>
    map_TT f x = VVr y \<longleftrightarrow> (\<exists>z. x = VVr z \<and> y = f z)"
  by (cases x)
    (auto simp: VVr_inj map_TT_VVr map_TT_comp[symmetric] supp_inv_bound map_TT_id
      dest!: arg_cong[of "map_TT f x" _ "map_TT (inv f)"])

lemma SSupp_comp_le:
  fixes u :: "'a \<Rightarrow> 'a :: vvar_TT" and f :: "'a \<Rightarrow> 'a TT"
  assumes u: "|supp u| <o bound (any :: 'a)"
  shows "SSupp (f o u) \<subseteq> SSupp f \<union> supp u"
  unfolding SSupp_def supp_def
  by (auto simp: map_TT_VVr assms)

lemma SSupp_comp_le2:
  fixes u :: "'a \<Rightarrow> 'a :: vvar_TT" and f :: "'a \<Rightarrow> 'a TT"
  assumes u: "bij u" "|supp u| <o bound (any :: 'a)"
  shows "SSupp (map_TT u o f) \<subseteq> SSupp f \<union> supp u"
  unfolding SSupp_def supp_def
  by (auto simp: map_TT_VVr assms)

lemma SSupp_comp_bound:
  fixes u :: "'a \<Rightarrow> 'a :: vvar_TT" and f :: "'a \<Rightarrow> 'a TT"
  assumes "|SSupp f| <o bound (any :: 'a)" and "|supp u| <o bound (any :: 'a)"
  shows "|SSupp (f o u)| <o bound (any :: 'a)"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_comp_le]])
    (auto simp: assms Un_bound)

lemma SSupp_comp_bound2:
  fixes u :: "'a \<Rightarrow> 'a :: vvar_TT" and f :: "'a \<Rightarrow> 'a TT"
  assumes u: "bij u" "|supp u| <o bound (any :: 'a)" and f: "|SSupp f| <o bound (any :: 'a)"
  shows "|SSupp (map_TT u o f)| <o bound (any :: 'a)"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_comp_le2]])
    (auto simp: assms Un_bound)

setup_lifting type_definition_SSfun

lift_definition vvrSS :: "'a :: vvar_TT SSfun" is VVr
  by (simp add: SSupp_VVr_bound)

context
  fixes u :: "'a :: vvar_TT \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o bound(any :: 'a)"
begin

lift_definition compSS :: "'a :: vvar_TT SSfun \<Rightarrow> 'a SSfun" is "\<lambda>p. map_TT u o p o inv u"
  by (auto simp: u supp_inv_bound SSupp_comp_bound SSupp_comp_bound2)

end

context
  fixes u :: "'a :: vvar_TT \<Rightarrow> 'a"
  assumes u[transfer_rule, simp]: "bij u" "|supp u| <o bound(any :: 'a)"
begin

lemma compSS_inv_compSS[simp]: "compSS (inv u) (compSS u p) = p"
  supply bij_imp_bij_inv[transfer_rule] supp_inv_bound[transfer_rule]
  apply transfer
  apply (auto simp: o_def map_TT_comp[symmetric] supp_inv_bound id_def[symmetric] map_TT_id)
  done

end

context
  fixes u v :: "'a :: vvar_TT \<Rightarrow> 'a"
  assumes [transfer_rule, simp]: "bij u" "|supp u| <o bound(any :: 'a)" "bij v" "|supp v| <o bound(any :: 'a)"
begin

lemma compSS_o[simp]: "compSS (u o v) p = compSS u (compSS v p)"
  supply bij_comp[transfer_rule] supp_comp_bound[transfer_rule]
  apply transfer
  apply (auto simp: o_inv_distrib fun_eq_iff map_TT_comp)
  done

end

lemma compSS_id[simp]: "compSS id = id"
  supply supp_id_bound[transfer_rule] bij_id[transfer_rule]
  by (rule ext, transfer) (auto simp: map_TT_id)

datatype 'a D = D "'a TT" "'a SSfun"

definition DDTOR :: "('a::vvar_TT D \<Rightarrow> ('a, 'a, 'a TT + 'a D , 'a TT + 'a D) F set)" where
  "DDTOR = (\<lambda>d. case d of D t f \<Rightarrow> if isVVr t then {map_F id id Inl Inl x | x. Rep_SSfun f (asVVr t) = cctor x}
      else
      {map_F id id (\<lambda>x. Inr (D x f)) (\<lambda>x. Inr (D x f)) x | x.
        t = cctor x \<and> set2_F x \<inter> IImsupp (Rep_SSfun f) = {}})"
definition mmapD :: "('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'a D \<Rightarrow> 'a D" where
  "mmapD = (\<lambda>u d. case d of D x f \<Rightarrow> D (map_TT u x) (compSS u f))"
definition FFVarsD :: "'a::vvar_TT D \<Rightarrow> 'a set" where
  "FFVarsD = (\<lambda>d. case d of D x f \<Rightarrow> FFVars x \<union> IImsupp (Rep_SSfun f))"

declare D.splits[split]

lemmas comodel_defs = DDTOR_def mmapD_def FFVarsD_def

(* Comodel properties: *)
lemma
  (* Full-corecursion version of the clauses (Dne), (MD), (VD) and (DRen) from the paper: *)
  DDTOR_ne: "DDTOR d \<noteq> {}"
  and 
  DDTOR_mmapD0: "{X,X'} \<subseteq> DDTOR d \<Longrightarrow> 
\<exists>u. bij (u::'a \<Rightarrow> 'a) \<and> |supp u| <o bound(any::'a::vvar_TT) \<and> id_on (UNION (set4_F X) (case_sum FFVars FFVarsD) - set2_F X) u \<and> 
     map_F id u id (map_sum (map_TT u) (mmapD u)) X = X'" 
  and   
  FFVarsD_DDTOR0: 
  "X \<in> DDTOR d \<Longrightarrow> 
  set1_F X \<union> UNION (set3_F X) (case_sum FFVars FFVarsD) \<union>
   (UNION (set4_F X) (case_sum FFVars FFVarsD) - set2_F X) \<subseteq> 
  FFVarsD d"  
  and  
  mmapD_DDTOR: "bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound(any::'a::vvar_TT) \<Longrightarrow> 
  DDTOR (mmapD u d) \<subseteq>
  image 
    (map_F u u (map_sum (map_TT u) (mmapD u)) (map_sum (map_TT u) (mmapD u))) 
    (DDTOR d)"
  and 
  (* Comodels are a restricted term-like structure: *)
  termLikeStr_mmapD_FFVarsD: "termLikeStrD mmapD"
  unfolding comodel_defs
      apply -
  subgoal
    by (auto split: prod.splits simp: TT_nchotomy fresh_nchotomy IImsupp_SSupp_bound Rep_SSfun[simplified])
  subgoal
    apply (clarsimp split: if_splits)
    subgoal
      apply (auto simp: TT_inject0 F_map_comp[symmetric] supp_id_bound F_set_map FFVars_map_TT)
      subgoal for u
        apply (rule exI[of _ "inv u"])
        apply (force simp: supp_inv_bound id_on_def image_iff F_map_comp[symmetric] supp_id_bound
            map_sum_def map_TT_comp[symmetric] o_def id_def[symmetric] map_TT_id)
        done
      done
    subgoal for p x y
      apply (subst (asm) TT_fresh_inject[of "IImsupp (Rep_SSfun p)"])
         apply (auto simp: IImsupp_SSupp_bound Rep_SSfun[simplified]) [3]
      apply safe
      subgoal for u
        apply (auto simp: supp_inv_bound supp_id_bound supp_comp_bound Rep_SSfun[simplified]
            F_set_map FFVars_map_TT F_map_comp[symmetric] id_on_def
            map_TT_id map_TT_comp[symmetric] bij_imp_inv
            intro!: exI[of _ "u"] F_map_cong)
         apply (auto simp: imsupp_def supp_def) []
        subgoal premises prems
          supply prems(7,8)[transfer_rule] supp_inv_bound[transfer_rule] bij_imp_bij_inv[transfer_rule]
          using prems(5,6,9,10)
          apply (transfer fixing: u)
          apply (auto simp: prems(7,8) fun_eq_iff)
          subgoal for x p a
            apply (auto simp: IImsupp_imsupp_map_TT_commute[of p u "inv u a"] prems(7,8))
            done
          done
        done
      done
    done
  subgoal
    apply (auto simp: F_set_map supp_id_bound Rep_SSfun[simplified] FFVars_simps isVVr_def FFVars_VVr
        asVVr_VVr split: if_splits)
      apply (auto simp: IImsupp_def SSupp_def)
      apply (metis FFVars_VVr FFVars_intros(1) singleton_iff)
     apply  (metis FFVars_VVr FFVars_intros(2) singleton_iff)
    apply (metis FFVars_VVr FFVars_intros(3) insertI1 insert_Diff_if insert_absorb singleton_iff)
    done
  subgoal
    apply (simp split: prod.splits if_splits, safe)
    subgoal
      apply (drule arg_cong[of _ _ "map_TT (inv u)"])
      apply (auto simp: isVVr_def map_TT_VVr VVr_inj
          image_iff asVVr_VVr compSS.rep_eq map_TT_cctor
          map_TT_comp[symmetric] supp_inv_bound map_TT_id)
      apply (rule exI conjI refl)+
      apply (auto simp: F_map_comp[symmetric] supp_id_bound Rep_ssfun[simplified]
          image_iff map_sum_def compSS.rep_eq supp_comp_bound supp_inv_bound F_set_map
          inv_o_simp1[THEN rewriteR_comp_comp] map_TT_comp[symmetric] map_TT_id
          split: sum.splits intro!: F_map_cong)
      done
    subgoal by (force simp: isVVr_def map_TT_VVr dest: sym)
    subgoal by (auto simp: isVVr_def map_TT_eq_VVr_iff)
    subgoal for t p _ x
      apply (drule arg_cong[of _ _ "map_TT (inv u)"])
      apply (auto simp: image_iff map_TT_comp[symmetric] supp_inv_bound map_TT_id map_TT_cctor)
      apply (rule exI conjI refl)+
       apply (auto simp: F_map_comp[symmetric] supp_id_bound Rep_ssfun[simplified]
          image_iff map_sum_def compSS.rep_eq supp_comp_bound supp_inv_bound F_set_map
          inv_o_simp1[THEN rewriteR_comp_comp] map_TT_comp[symmetric] map_TT_id
          split: sum.splits intro!: F_map_cong)
      apply (simp add: disjoint_iff_not_equal)
      apply (drule bspec, assumption)
      apply (auto simp: IImsupp_def SSupp_def ball_Un FFVars_map_TT)
      subgoal for x
        apply (drule spec[of _ x])+
        apply (auto simp: supp_inv_bound map_TT_comp[symmetric] map_TT_id map_TT_VVr
          dest!: arg_cong[of _ "VVr x" "map_TT (inv u)"]) []
        done
      subgoal for _ x
        apply (drule spec[of _ "u x"])+
        apply (auto simp: supp_inv_bound map_TT_comp[symmetric] map_TT_id map_TT_VVr
          dest!: arg_cong[of _ "VVr (u x)" "map_TT (inv u)"])
        done
      done
    done
  subgoal
    apply (auto simp: map_TT_id map_TT_comp)
    done
  done


(* Defined analogously to the FVarsB: *)
definition FFVarsBD :: "('a::vvar_TT, 'a, 'a TT + 'a D, 'a TT + 'a D) F \<Rightarrow> 'a set" where
  "FFVarsBD X \<equiv> UNION (set4_F X) (case_sum FFVars FFVarsD) - set2_F X"

lemmas DDTOR_mmapD = DDTOR_mmapD0[folded FFVarsBD_def]
lemmas FFVarsD_DDTOR = FFVarsD_DDTOR0[folded FFVarsBD_def]

(*  *)
lemma mmapD_id[simp,intro!]: "mmapD id d = d"
  using termLikeStr_mmapD_FFVarsD by auto

lemma mmapD_comp: 
  "bij (u::'a\<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::vvar_TT) \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o bound (any::'a) \<Longrightarrow> 
 mmapD (u o v) d = mmapD u (mmapD v d)"
  using termLikeStr_mmapD_FFVarsD by auto

(*  *)

lemma mmapD_DDTOR_strong: 
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::vvar_TT)"
  shows
    "DDTOR (mmapD u d) =
 image 
   (map_F u u (map_sum (map_TT u) (mmapD u)) (map_sum (map_TT u) (mmapD u))) 
   (DDTOR d)" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R" using mmapD_DDTOR[OF assms] .
next
  have iu: "bij (inv u)" "|supp (inv u)| <o bound(any::'a)" using u by(simp_all add: supp_inv_bound) 
  define dd where "dd \<equiv> mmapD u d"
  have d: "d = mmapD (inv u) dd" 
    using u unfolding dd_def by(simp add: mmapD_comp[symmetric] supp_inv_bound) 
  have [simp]: "mmapD u \<circ> (mmapD (inv u)) = id" unfolding fun_eq_iff
    by (simp add: u iu mmapD_comp[symmetric])
  show "?R \<subseteq> ?L" unfolding dd_def[symmetric] d using mmapD_DDTOR[OF iu, of dd] 
    by(auto simp: u iu F_map_comp[symmetric] 
        map_sum.comp TT_map_o[symmetric] map_TT_id mmapD_comp[symmetric] map_sum.id F_map_id) 
qed


(*************************************)
(* The raw-term-based model infrastructure *)  

definition DTOR :: "'a::vvar_TT D \<Rightarrow> ('a, 'a, 'a T + 'a D, 'a T + 'a D) F set" where 
  "DTOR d \<equiv>  map_F id id (map_sum rep_TT id) (map_sum rep_TT id) ` (DDTOR d)"

abbreviation mapD :: "('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'a D \<Rightarrow> 'a D" where 
  "mapD \<equiv> mmapD"  

abbreviation FVarsD :: "'a::vvar_TT D \<Rightarrow> 'a set" where 
  "FVarsD \<equiv> FFVarsD" 

definition FVarsBD :: "('a::vvar_TT, 'a, 'a T + 'a D, 'a T + 'a D) F \<Rightarrow> 'a set" where 
  "FVarsBD X \<equiv> UNION (set4_F X) (case_sum FVars FVarsD) - set2_F X"

lemmas FVars_def2 = FFVars.abs_eq[symmetric]


(* Raw-term-based version of the assumptions: *)

(*  *)
lemmas mapD_id = mmapD_id 

lemmas mapD_comp = mmapD_comp 

lemma FVarsBD_FFVarsBD: 
  "FVarsBD X = FFVarsBD (map_F id id (map_sum abs_TT id) (map_sum abs_TT id) X)"
  unfolding FVarsBD_def FFVarsBD_def FVars_def2   
  apply(simp add: F_set_map FVars_def2 case_sum_map_sum supp_id_bound) 
  unfolding o_def id_def ..

lemma DTOR_mapD: 
  assumes "{X,X'} \<subseteq> DTOR d"
  shows "\<exists>u. bij (u::'a\<Rightarrow>'a) \<and> |supp u| <o bound(any::'a::vvar_TT) \<and> id_on (FVarsBD X) u \<and> 
     rel_F id u 
       (rel_sum alpha (=)) 
       (rel_sum (\<lambda> t t'. alpha (map_T u t) t') (\<lambda> d d'. mapD u d = d')) 
     X X'"  
proof-
  define XX XX' where 
    "XX \<equiv> map_F id id (map_sum abs_TT id) (map_sum abs_TT id) X" and 
    "XX' \<equiv> map_F id id (map_sum abs_TT id) (map_sum abs_TT id) X'" 
  have 0: "{XX,XX'} \<subseteq> DDTOR d" using assms unfolding XX_def XX'_def DTOR_def
    by (auto simp: F_map_comp[symmetric] map_sum.comp abs_rep_TT map_sum.id F_map_id supp_id_bound)       
  then obtain u where u: "bij u" "|supp u| <o bound(any::'a)" "id_on (FFVarsBD XX) u"
    and m: "map_F id u id (map_sum (map_TT u) (mmapD u)) XX = XX'"
    using DDTOR_mmapD[OF 0] by auto 
  have [simp]: "asSS (asBij u) = u"  "asSS u = u" using u unfolding asSS_def by auto
  show ?thesis
  proof(rule exI[of _ u], safe )
    show "id_on (FVarsBD X) u"  
      using u(3) unfolding id_on_def XX_def FVarsBD_FFVarsBD by auto
    show "rel_F id u (rel_sum alpha (=)) (rel_sum (\<lambda>t. alpha (map_T u t)) (\<lambda>d d'. mapD u d = d')) X X'"
      using m unfolding XX_def XX'_def
      apply(simp add: u F_map_comp[symmetric] F_map_id map_sum.comp map_TT_def F.rel_eq[symmetric]
          F_rel_map supp_id_bound)
      apply(rule F_rel_mono_strong1) apply (auto simp: u supp_id_bound)
      unfolding Grp_def apply auto
      subgoal for d1 d2
        using TT.abs_eq_iff apply(cases d1) by (cases d2,fastforce, fastforce)+
      subgoal for d1 d2
        using TT.abs_eq_iff abs_TT_alpha_aux[OF u(1,2)] 
        apply(cases d1) apply(cases d2) apply auto 
        apply(cases d2) by auto .
  qed(insert u, auto)
qed

lemma DTOR_ne: 
  "DTOR d \<noteq> {}"
  unfolding DTOR_def using DDTOR_ne by auto

lemma FVarsD_DTOR: 
  assumes "X \<in> DTOR d"
  shows "set1_F X \<union> UNION (set3_F X) (case_sum FVars FVarsD) \<union> FVarsBD X \<subseteq> FVarsD d"
proof-
  define XX where "XX \<equiv> map_F id id (map_sum abs_TT id) (map_sum abs_TT id) X"  
  have 0: "XX \<in> DDTOR d" using assms unfolding XX_def DTOR_def 
    by (auto simp: F_map_comp[symmetric] map_sum.comp abs_rep_TT map_sum.id F_map_id supp_id_bound) 
  show ?thesis using FFVarsD_DDTOR[OF 0] unfolding FVarsBD_FFVarsBD XX_def
    apply (simp add: F_set_map FVars_def2 case_sum_map_sum supp_id_bound) unfolding FVars_def2 o_def 
      map_sum.simps id_def by simp
qed

lemma rel_set_reflI: 
  assumes "\<And>a. a \<in> A \<Longrightarrow> r a a"
  shows "rel_set r A A"
  using assms unfolding rel_set_def by auto

lemma mapD_DTOR: 
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::vvar_TT)"
  shows 
    "rel_set
  (rel_F u u 
     (rel_sum (\<lambda> t t'. alpha (map_T u t) t') (\<lambda> d d'. mapD u d = d'))
     (rel_sum (\<lambda> t t'. alpha (map_T u t) t') (\<lambda> d d'. mapD u d = d')))
 (DTOR d)
 (DTOR (mapD u d))" 
  unfolding DTOR_def  
  by (auto intro!: rel_set_reflI F.rel_refl_strong sum.rel_refl_strong 
      simp: mmapD_DDTOR_strong[OF u, of d] rel_set_image u F_rel_map OO_def Grp_def sum.rel_map 
      map_TT_def asSS_def alpha_rep_abs_TT alpha_sym
      image_comp F_map_comp1[symmetric] map_sum.comp supp_id_bound)  

(*    *)

definition suitable ::  "('a::vvar_TT D \<Rightarrow> ('a,'a,'a T + 'a D,'a T + 'a D)F) \<Rightarrow> bool" where
  "suitable pick \<equiv> \<forall> d. pick d \<in> DTOR d"

definition f :: "('a::vvar_TT D \<Rightarrow> ('a,'a,'a T + 'a D,'a T + 'a D)F) \<Rightarrow> 'a D => 'a T" where
  "f pick \<equiv> corec_T pick"
thm T.corec[of "pick o DTOR", unfolded f_def[symmetric]]

lemma f_simps: 
  "f pick d = ctor (map_F id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d))"
  apply(subst T.corec[of pick, unfolded f_def[symmetric]]) unfolding id_def ..

lemma f_ctor: 
  "ctor x = f pick d \<Longrightarrow> 
 x = map_F id id (case_sum id (f pick)) (case_sum id (f pick)) (pick d)"
  using f_simps[of pick d] by simp

lemma suitable_FVarsD:
  assumes "suitable pick"  
  shows "set1_F (pick d) \<union> UNION (set3_F (pick d)) (case_sum FVars FVarsD) \<union> FVarsBD (pick d)
       \<subseteq> FVarsD d"
  using FVarsD_DTOR[of "pick d"] using assms[unfolded suitable_def] by auto

(*  *)

lemma f_FVarsD: 
  assumes p: "suitable pick"  
  shows "FVars (f pick d) \<subseteq> FVarsD d"
proof safe
  fix a assume aa: "a \<in> FVars (f pick d)"  
  define t where "t = f pick d"
  show "a \<in> FVarsD d" using aa[unfolded t_def[symmetric]] using t_def
  proof(induction arbitrary: d)
    case (set1 a x)
    note x = f_ctor[OF `ctor x = f pick d`] 
    note fvd = suitable_FVarsD[OF assms, of d]
    show ?case using set1.hyps fvd unfolding x by (auto simp add: F_set_map supp_id_bound)
  next
    case (set2_free t x a)
    note x = f_ctor[OF `ctor x = f pick d`]  
    note fvd = suitable_FVarsD[OF assms, of d]
    from `t \<in> set3_F x` obtain td where t: "t = case_sum id (f pick) td" 
      and td: "td \<in> set3_F (pick d)" unfolding x by (auto simp add: F_set_map supp_id_bound)
    have a: "a \<in> case_sum FVars FVarsD td"
      using set2_free.IH set2_free.hyps unfolding t by(cases td) auto
    show ?case using a td by (intro rev_subsetD[OF _ fvd]) auto 
  next
    case (set2_rec t x a d)
    note x = f_ctor[OF `ctor x = f pick d`]  
    note fvd = suitable_FVarsD[OF assms, of d]
    from `t \<in> set4_F x` obtain td where t: "t = case_sum id (f pick) td" 
      and td: "td \<in> set4_F (pick d)" unfolding x by (auto simp add: F_set_map supp_id_bound)
    have a: "a \<in> case_sum FVars FVarsD td"
      using set2_rec.IH set2_rec.hyps unfolding t by(cases td) auto
    have "a \<notin> set2_F (pick d)" using `a \<notin> set2_F x` unfolding x by(auto simp: F_set_map supp_id_bound)
    thus ?case using a td apply (intro rev_subsetD[OF _ fvd]) unfolding FVarsBD_def by auto 
  qed
qed


lemma rel_F_suitable_mapD: 
  assumes pp': "suitable pick" "suitable pick'"
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::vvar_TT)"
  shows "\<exists> v. bij v \<and> |supp v| <o bound(any::'a) \<and> id_on (FVarsBD (pick d)) v \<and> 
 rel_F u (u o v)   
   (rel_sum (\<lambda>t t'. alpha (map_T u t) t') 
            (\<lambda>d d'. d' = mapD u d))
   (rel_sum (\<lambda>t t'. alpha (map_T (u o v) t) t') 
            (\<lambda>d d'. mapD (u o v) d = d'))
 (pick d)  
 (pick' (mapD u d))" 
proof- 
  have p: "pick d \<in> DTOR d" and p': "pick' (mapD u d) \<in> DTOR (mapD u d)" 
    using pp' unfolding suitable_def by auto
  obtain X where X: "X \<in> DTOR d" and 0: 
    "rel_F u u 
       (rel_sum (\<lambda>t. alpha (map_T u t)) (\<lambda>d. (=) (mapD u d)))
       (rel_sum (\<lambda>t. alpha (map_T u t)) (\<lambda>d. (=) (mapD u d)))
     X (pick' (mapD u d))"
    using mapD_DTOR[OF u, of d] p' unfolding rel_set_def by auto
  obtain v where v: "bij v" "|supp v| <o bound(any::'a)" "id_on (FVarsBD (pick d)) v" 
    and 2: 
    "rel_F id v 
      (rel_sum alpha (=)) 
      (rel_sum (\<lambda>t. alpha (map_T v t)) (\<lambda>d. (=) (mapD v d))) 
   (pick d) X" using DTOR_mapD[of "pick d" X d] using pp' X unfolding suitable_def by auto
  show ?thesis apply(rule exI[of _ v], simp add: v)
    apply(rule F_rel_mono_strong1[OF _ _ _ F_rel_comp_imp[OF _ _ _ _ _ _ 2 0], simplified])
           apply(auto simp: u v supp_comp_bound supp_inv_bound supp_id_bound)
    subgoal for td1 td3 td2 using alpha_refl
      apply(cases td1) apply auto 
       apply(cases td2) apply auto  apply(cases td3) apply auto
       apply (smt alpha_bij_eq alpha_trans rel_sum_simps(1) u(1) u(2))
      apply(cases td2) apply auto  apply(cases td3) by auto 
    subgoal for td1 td3 td2 using alpha_refl
      apply(cases td1) apply auto 
       apply(cases td2) apply auto  apply(cases td3) apply (auto  simp: u v T_map_comp supp_inv_bound 
          ) using alpha_bij_eq alpha_trans  using u(1) u(2) apply blast
      apply(cases td2) apply auto  apply(cases td3) 
      by (auto simp: u v T_map_comp mapD_comp[symmetric]) . 
qed

(* The "monster lemma": termLikeStr and "pick"-irrelevance covered in one shot: *)

lemma f_swap_alpha: 
  assumes p: "suitable pick" and p': "suitable pick'"
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::vvar_TT)" 
  shows "alpha (map_T u (f pick d)) (f pick' (mapD u d))"
proof- 
  let ?\<phi> = "\<lambda> tL tR. \<exists> u d. bij u \<and> |supp u| <o bound(any::'a) \<and> 
   tL = map_T u (f pick d) \<and> tR = f pick' (mapD u d)"
  {fix tL tR assume "?\<phi> tL tR"
    hence "alpha tL tR"
    proof(induction rule: alpha_coinduct2)
      case (C xL xR)  
      then obtain u d
        where u: "bij u" "|supp u| <o bound(any::'a)"  
          and "ctor xL = map_T u (f pick d)" "ctor xR = f pick' (mapD u d)" by auto
      hence xL: "xL = map_F u u (map_T u \<circ> case_sum id (f pick)) (map_T u\<circ> case_sum id (f pick)) (pick d)" 
        and xR: "xR = map_F id id (case_sum id (f pick')) (case_sum id (f pick')) (pick' (mapD u d))"
        using f_simps[of "pick"] f_simps[of "pick'"] 
        by (auto simp: u map_T_simps F_map_comp[symmetric] supp_id_bound)
          (*  *)
      obtain v where v: "bij v" "|supp v| <o bound(any::'a)" and iv: "id_on (FVarsBD (pick d)) v"
        and rv:   
        "rel_F u (u \<circ> v) 
       (rel_sum (\<lambda>t. alpha (map_T u t)) (\<lambda>d d'. d' = mapD u d))
       (rel_sum (\<lambda>t. alpha (map_T (u \<circ> v) t)) (\<lambda>d. (=) (mapD (u \<circ> v) d))) 
     (pick d) (pick' (mapD u d)) " 
        using rel_F_suitable_mapD[OF p p' u(1,2)] by blast 
      define w where "w \<equiv> u o v o inv u" 
      have w: "bij w" "|supp w| <o bound(any::'a)" by (simp_all add: w_def u v supp_comp_bound supp_inv_bound)
      have fv_xL: "FVarsB xL \<subseteq> u ` (FVarsBD (pick d))" 
        using f_FVarsD[OF p] unfolding xL apply (auto simp: u F_set_map FVars_map_T FVarsBD_def)
        subgoal for td a apply (cases td) by fastforce+ . 
      have fv_p'd: "FVarsBD (pick d) \<subseteq> FVarsD d" 
        using FVarsD_DTOR[of "pick d"] p unfolding suitable_def by auto
      have "id_on (u ` (FVarsBD (pick d))) w"
        using iv fv_p'd unfolding id_on_def xL w_def eq_on_def id_on_def by (auto simp: F_set_map u) 
      hence iw: "id_on (FVarsB xL) w" using fv_xL unfolding id_on_def by auto 
      show ?case proof(rule exI[of _ w], safe)
        show "rel_F id w
      (\<lambda>t t'. (\<exists>u d. bij u \<and> |supp u| <o bound(any::'a) \<and>   
                     t = map_T u (f pick d) \<and> t' = f pick' (mapD u d))
              \<or> alpha t t')
      (\<lambda>t t'. (\<exists>u d. bij u \<and> |supp u| <o bound(any::'a) \<and> 
                     map_T w t = map_T u (f pick d)  \<and> t' = f pick' (mapD u d))
              \<or> alpha (map_T w t) t')
      xL xR" unfolding xL xR  
          apply(simp add: w u F_rel_map Grp_def OO_def supp_comp_bound supp_inv_bound T_map_comp[symmetric] supp_id_bound)
        proof(rule F_rel_mono_strong0[OF _ _ _ _ _ _ rv], auto)  
          fix a assume "a \<in> set2_F (pick d)"
          thus "u (v a) = w (u a)"  
            unfolding w_def by (simp add: u v)
        next
          fix ttdL ttdR assume ttdLin: "ttdL \<in> set3_F (pick d)"
            and ttdRin: "ttdR \<in> set3_F (pick' (mapD u d))"
            and r: "rel_sum (\<lambda>t. alpha (map_T u t)) (\<lambda>d d'. d' = mapD u d) ttdL ttdR"
            and na: "\<not> alpha (map_T u (case_sum id (f pick) ttdL)) (case_sum id (f pick') ttdR)"
          {fix tL assume 000: "ttdL = Inl tL" 
            then obtain tR where "ttdR = Inl tR"
              and  "alpha (map_T u tL) tR" "\<not> alpha (map_T u tL) tR" using r na by (cases ttdR, auto)
            moreover have "alpha (map_T u tL) (map_T u tL)" 
              apply(rule alpha_cong) by (auto simp: u)  
            ultimately have False using alpha_trans alpha_sym by blast
          }
          then obtain dd where ttdL: "ttdL = Inr dd" by (cases ttdL, auto)
          hence ttdR: "ttdR = Inr (mapD u dd)" using r by(cases ttdR, auto)
          have fv_dd: "FVarsD dd \<subseteq> FVarsD d" using ttdLin unfolding ttdL 
            using FVarsD_DTOR p unfolding suitable_def by force        
          show "\<exists>uu. bij uu \<and> |supp uu| <o bound(any::'a) \<and>
             (\<exists> dd. map_T u (case_sum id (f pick) ttdL) = map_T uu (f pick dd) \<and>
                    case_sum id (f pick') ttdR = f pick' (mapD uu dd))"
            by (auto simp: u ttdL ttdR intro: exI[of _ u] exI[of _ dd])
        next
          fix ttdL ttdR assume ttdLin: "ttdL \<in> set4_F (pick d)"
            and ttdRin: "ttdR \<in> set4_F (pick' (mapD u d))"
            and r: "rel_sum (\<lambda>t. alpha (map_T (u \<circ> v) t)) (\<lambda>d. (=) (mapD (u \<circ> v) d)) ttdL ttdR"
            and na: "\<not> alpha (map_T (w \<circ> u) (case_sum id (f pick) ttdL)) (case_sum id (f pick') ttdR)"
          have uvw: "u \<circ> v = w \<circ> u" unfolding w_def by (auto simp: u)
          {fix tL assume 000: "ttdL = Inl tL" 
            then obtain tR where "ttdR = Inl tR"
              and  "alpha (map_T (u \<circ> v) tL) tR" "\<not> alpha (map_T (w \<circ> u) tL) tR" 
              using r na by (cases ttdR, auto)
            moreover have "alpha (map_T (u \<circ> v) tL) (map_T (w \<circ> u) tL)" 
              unfolding uvw using alpha_refl .   
            ultimately have False using alpha_trans alpha_sym by blast
          }
          then obtain dd where ttdL: "ttdL = Inr dd" by (cases ttdL, auto)
          hence ttdR: "ttdR = Inr (mapD (u \<circ> v) dd)" using r by (cases ttdR, auto)        
          show "\<exists>uu. bij uu \<and> |supp uu| <o bound(any::'a) \<and>
              (\<exists> dd. map_T (w \<circ> u) (case_sum id (f pick) ttdL) = map_T uu (f pick dd) \<and>
                     case_sum id (f pick') ttdR = f pick' (mapD uu dd))"  
            by (auto simp: u w supp_comp_bound ttdL ttdR uvw intro: exI[of _ "w o u"] exI[of _ dd]) 
        qed(simp_all add: w u v supp_comp_bound)
      qed(simp_all add: w iw)
    qed 
  }
  thus ?thesis using assms by blast
qed

lemma f_alpha: 
  assumes p: "suitable pick" and p': "suitable pick'" 
  shows "alpha (f pick d) (f pick' d)"
  using f_swap_alpha[OF assms bij_id supp_id_bound, of d] by (simp add: T_map_id) 

(*******************************)
(* Committing to a particular pick function: *)

definition pick0 :: "'a::vvar_TT D \<Rightarrow> ('a, 'a, 'a T + 'a D, 'a T + 'a D) F" where
  "pick0 \<equiv> SOME pick. suitable pick"

lemma exists_suitable: 
  "\<exists> pick. suitable pick" 
proof-
  have "\<forall>d. \<exists> X. X \<in> DTOR d" using DTOR_ne by auto
  thus ?thesis unfolding suitable_def by metis
qed

lemma suitable_pick0:
  "suitable pick0"
  using someI_ex[OF exists_suitable] unfolding pick0_def[symmetric] .

definition f0 where "f0 \<equiv> f pick0"

lemmas f0_low_level_simps = f_simps[of pick0, unfolded f0_def[symmetric]]

lemma f0_DTOR: 
  assumes "X \<in> DTOR d"
  shows "alpha (f0 d) (ctor (map_F id id (case_sum id f0) (case_sum id f0) X))"
proof-  
  define pick1 where "pick1 \<equiv> \<lambda> d'. if d' = d then X else pick0 d'"
  have 1: "suitable pick1" using suitable_pick0 assms unfolding suitable_def pick1_def by auto
  have 2: "pick1 d = X" unfolding pick1_def by auto
  have 3: "\<And> dd. alpha (f0 dd) (f pick1 dd)" using f_alpha[OF suitable_pick0 1, of ] 
    unfolding f0_def[symmetric] .
  have 4: "f pick1 d = ctor (map_F id id (case_sum id (f pick1)) (case_sum id (f pick1)) X)"
    apply(subst f_simps) unfolding 2 ..
  have 5: "alpha (ctor (map_F id id (case_sum id (f pick1)) (case_sum id (f pick1)) X)) 
                       (ctor (map_F id id (case_sum id f0) (case_sum id f0) X))"
    apply(rule alpha.intros[of id]) apply (auto simp: F_rel_map simp: Grp_def OO_def supp_id_bound)
    apply(rule F.rel_refl_strong)
    subgoal for td by (cases td, auto simp: alpha_refl alpha_sym[OF 3])
    subgoal for td by (cases td, auto simp: T_map_id alpha_refl alpha_sym[OF 3]) .
  show ?thesis using 3[of d] 5 unfolding 4[symmetric] using alpha_trans by blast
qed

lemma f0_mapD: 
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o bound(any::'a::vvar_TT)"  
  shows "alpha (f0 (mapD u d)) (map_T u (f0 d))" 
  using alpha_sym[OF f_swap_alpha[OF suitable_pick0 suitable_pick0 assms, unfolded f0_def[symmetric]]] .

lemmas f0_FVarsD = f_FVarsD[OF suitable_pick0, unfolded f0_def[symmetric]]


(* The following theorems for raw terms will now be lifted to quotiented terms: *)
thm f0_DTOR f0_mapD f0_FVarsD 

(*******************)
(* End product: *)
definition ff0 :: "'a::vvar_TT D \<Rightarrow> 'a TT" where "ff0 d = abs_TT (f0 d)" 

theorem ff0_DDTOR: 
  assumes "X \<in> DDTOR d"
  shows "ff0 d = cctor (map_F id id (case_sum id ff0) (case_sum id ff0) X)"
  using assms using DTOR_def
proof-
  define XX where "XX \<equiv> map_F id id (map_sum rep_TT id) (map_sum rep_TT id) X"
  have XX: "XX \<in> DTOR d" using assms unfolding XX_def DTOR_def by auto
  have 0: "alpha 
    (ctor (map_F id id (case_sum rep_TT f0) (case_sum rep_TT f0) X))
    (ctor (map_F id id (case_sum rep_TT (rep_TT \<circ> (abs_TT \<circ> f0))) 
                       (case_sum rep_TT (rep_TT \<circ> (abs_TT \<circ> f0))) X))" 
    apply(rule alpha.intros[of id]) apply (auto simp: F_rel_map Grp_def OO_def supp_id_bound)
    apply(rule F.rel_refl_strong)
    subgoal for td by (cases td) (auto simp add: alpha_refl alpha_rep_abs_TT alpha_sym)  
    subgoal for td by (cases td) (auto simp add: alpha_refl alpha_rep_abs_TT alpha_sym T_map_id) .
  show ?thesis using f0_DTOR[OF XX] unfolding ff0_def cctor_def 
    apply(auto simp: F_map_comp[symmetric] supp_id_bound id_def[symmetric] XX_def  
        TT.abs_eq_iff o_case_sum case_sum_o_map_sum)   
    unfolding o_def[symmetric] using alpha_trans[OF _ 0] by auto
qed

lemma ff0_mmapD: 
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o bound(any::'a::vvar_TT)"  
  shows "ff0 (mmapD u d) = map_TT u (ff0 d)" 
proof-
  {assume "alpha (f0 (mmapD u d)) (map_T u (f0 d))"
    moreover have "alpha (map_T u (f0 d)) (map_T u (rep_TT (abs_TT (f0 d))))" 
      unfolding alpha_bij_eq[OF assms] by (simp add: alpha_rep_abs_TT alpha_sym)
    ultimately have "alpha (f0 (mmapD u d)) (map_T u (rep_TT (abs_TT (f0 d))))" 
      using alpha_trans by blast
  }
  thus ?thesis using f0_mapD[OF assms, of d]
    unfolding ff0_def map_TT_def by(auto simp: TT.abs_eq_iff asSS_def asBij_def assms)
qed

theorem ff0_FFVarsD: 
  "FFVars (ff0 d) \<subseteq> FFVarsD d"
  using f0_FVarsD[of d] alpha_FVars alpha_rep_abs_TT 
  unfolding ff0_def FFVars_def by fastforce

hide_const f

context
  fixes f :: "'a :: vvar_TT \<Rightarrow> 'a TT"
  assumes f: "|SSupp f| <o bound (any :: 'a)"
begin

lift_definition fSS :: "'a SSfun" is f by (rule f)

definition tvsubst where "tvsubst x = ff0 (D x fSS)"

lemma tvsubst_VVr: "tvsubst (VVr x) = f x"
  unfolding tvsubst_def
  by (subst ff0_DDTOR[unfolded comodel_defs, of "map_F id id Inl Inl (SOME F. f x = cctor F)"])
    (auto simp add: isVVr_def asVVr_VVr VVr_inj fSS.rep_eq
     F_map_comp[symmetric] supp_id_bound case_sum_o_inj F.map_id
     someI_ex[OF TT_nchotomy[rule_format, of "f x"], symmetric])

lemma tvsubst_cctor_not_isVVr: "set2_F x \<inter> (IImsupp f) = {} \<Longrightarrow>
  \<not> isVVr (cctor x) \<Longrightarrow> tvsubst (cctor x) = cctor (map_F id id tvsubst tvsubst x)"
  unfolding tvsubst_def
  by (subst ff0_DDTOR[unfolded comodel_defs])
    (auto simp: F_map_comp[symmetric] f supp_id_bound o_def id_def[symmetric] fSS.rep_eq)

lemma FFVars_vvsubst_weak: "FFVars (tvsubst t) \<subseteq> FFVars t \<union> IImsupp f"
  unfolding tvsubst_def
  by (rule order_trans[OF ff0_FFVarsD[unfolded comodel_defs]])
    (auto simp: F_map_comp[symmetric] f supp_id_bound o_def id_def[symmetric] Rep_SSfun fSS.rep_eq)

end

thm vvsubst_cctor FFVars_vvsubst_weak

lemma IImsupp_empty_IntD1: "A \<inter> IImsupp f = {} \<Longrightarrow> x \<in> A \<Longrightarrow> f x = VVr x"
  unfolding IImsupp_def SSupp_def by auto
lemma IImsupp_empty_IntD2: "A \<inter> IImsupp f = {} \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> FFVars (f a) \<Longrightarrow> f a = VVr a"
  unfolding IImsupp_def SSupp_def by auto

lemma map_TT_tvsubst:
  fixes f :: "'a :: vvar_TT \<Rightarrow> 'a TT" and u :: "'a \<Rightarrow> 'a"
  assumes f: "|SSupp f| <o bound (any :: 'a)" and u: "bij u" "|supp u| <o bound (any :: 'a)"
  shows "map_TT u (tvsubst f t) = tvsubst (map_TT u o f o inv u) (map_TT u t)"
  unfolding tvsubst_def[OF f] ff0_mmapD[unfolded comodel_defs, OF u, symmetric]
  by (auto simp: tvsubst_def assms ff0_mmapD[unfolded comodel_defs, symmetric] SSupp_comp_bound SSupp_comp_bound2
      supp_inv_bound fSS_def compSS_def Abs_SSfun_inverse)

lemma FFVars_tvsubst_le:
  "a \<in> FFVars u \<Longrightarrow> \<forall>x (f :: 'a::vvar_TT \<Rightarrow> 'a TT).
   u = tvsubst f (cctor x) \<longrightarrow> |SSupp f| <o bound(any::'a) \<longrightarrow> set2_F x \<inter> IImsupp f = {} \<longrightarrow>
   a \<in> (\<Union>a \<in> FFVars (cctor x). FFVars (f a))"
  apply (induct a u rule: FFVars_induct[rule_format, consumes 1]; (rule allI impI)+)
  subgoal for a fx x f
    apply (cases "isVVr (cctor x)")
    apply (drule sym)
     apply (auto simp only: isVVr_def tvsubst_VVr FFVars_VVr UN_iff bex_simps
       intro!: FFVars_intros(1)) []
    apply (auto simp only: F_set_map tvsubst_cctor_not_isVVr simp_thms UN_iff
        bij_id supp_id_bound imsupp_supp_bound TT_inject0 image_id id_apply not_isVVr_set1_F
        dest!: arg_cong[of _ _ set1_F])
    done
  subgoal for fx u a x f
    apply (cases "isVVr (cctor x)")
    apply (drule sym)
     apply (auto simp only: isVVr_def tvsubst_VVr FFVars_VVr UN_iff bex_simps
       intro!: FFVars_intros(2)) []
    apply (auto simp only: F_set_map TT_inject0 tvsubst_cctor_not_isVVr simp_thms
        supp_id_bound bij_id image_id id_apply dest!: arg_cong[of _ _ set3_F])
    subgoal for v y
      apply (rule fresh_cases[of "IImsupp f" y])
       apply (simp only: IImsupp_SSupp_bound)
      apply (drule spec2, drule mp, hypsubst, rule refl)
      apply (auto simp only: intro!: imageI FFVars_intros(2))
      done
    done
  subgoal for fx u a x f
    apply (cases "isVVr (cctor x)")
    apply (drule sym)
     apply (auto simp only: isVVr_def tvsubst_VVr FFVars_VVr UN_iff bex_simps
       intro!: FFVars_intros(3)) []
    apply (auto simp only: F_set_map TT_inject0 tvsubst_cctor_not_isVVr simp_thms
        supp_id_bound bij_id image_id id_apply)
    apply (frule arg_cong[of _ _ set2_F, symmetric])
    apply (drule arg_cong[of _ _ set4_F])
    apply (auto simp only: F_set_map TT_inject0 vvsubst_cctor
        supp_id_bound bij_id image_id id_apply)
    subgoal for v
      apply (drule arg_cong[of _ _ "image (map_TT (inv v))"])
      apply (auto simp: image_image map_TT_comp[symmetric] map_TT_id supp_inv_bound
          map_TT_tvsubst)
      subgoal for u
        apply (rule fresh_cases[of "IImsupp f" u])
         apply (simp only: IImsupp_SSupp_bound)
        apply (hypsubst)
        apply (auto simp: map_TT_cctor supp_inv_bound)
        apply (drule spec2, drule mp, rule refl)
        apply (drule mp)
         apply (simp only: SSupp_comp_bound SSupp_comp_bound2 supp_inv_bound bij_imp_bij_inv)
        apply (drule mp)
         apply (auto simp: F_set_map supp_inv_bound) []
           apply (auto simp: IImsupp_def SSupp_def map_TT_eq_VVr_iff supp_inv_bound FFVars_map_TT bij_inv_rev) []
         apply (auto simp: map_TT_cctor[symmetric] supp_inv_bound FFVars_map_TT)
        apply (auto simp: bij_inv_rev intro!: bexI[rotated, OF FFVars_intros(3)])
        subgoal for y b
          apply (unfold disjoint_iff_not_equal)
          apply (drule bspec, rule imageI, assumption)
          apply (drule bspec[of "IImsupp f" _ "v b"])
          apply (auto simp: IImsupp_def SSupp_def FFVars_VVr)
          done
         apply (auto simp: id_on_def)
        done
      done
    done
  done

lemma FFVars_vvsubst_ge:
  fixes f::"'a::vvar_TT\<Rightarrow>'a TT"
  assumes "|SSupp f| <o bound(any::'a)"
  shows "a \<in> FFVars t \<Longrightarrow>  \<forall>x g. |supp g| <o bound(any::'a) \<longrightarrow> bij g  \<longrightarrow> g a = a \<longrightarrow>
    t = map_TT (inv g) (cctor x) \<longrightarrow> set2_F x \<inter> IImsupp f = {} \<longrightarrow>
    FFVars (f a) \<subseteq> FFVars (tvsubst f (cctor x))"
  apply (induct rule: FFVars_induct[rule_format, consumes 1]; (rule allI impI)+)
  subgoal for _ _ x
    apply (cases "isVVr (cctor x)")
     apply (auto simp: isVVr_def tvsubst_VVr assms map_TT_VVr supp_inv_bound) []
     apply (metis FFVars_VVr FFVars_intros(1) bij_pointE inv_simp1 singletonD)
    apply (auto simp: tvsubst_cctor_not_isVVr assms F_set_map supp_id_bound supp_inv_bound TT_inject0
        not_isVVr_set1_F map_TT_cctor image_iff bij_inv_rev
        dest!: arg_cong[of _ _ set1_F] intro!: FFVars_intros(1))
    done
  subgoal for fx t a x g
    apply (cases "isVVr (cctor x)")
     apply (drule sym[of "cctor fx"])
     apply (auto simp only: isVVr_def tvsubst_VVr FFVars_VVr UN_iff bex_simps assms map_TT_VVr
        supp_inv_bound bij_imp_bij_inv) []
     apply (auto simp: VVr_def TT_inject0 F_set_map supp_id_bound \<eta>_set3_F) []
    apply (auto simp: tvsubst_cctor_not_isVVr assms F_set_map supp_id_bound supp_inv_bound imsupp_supp_bound
        TT_inject0 map_TT_cctor FFVars_map_TT dest!: arg_cong[of _ _ set3_F])
    subgoal for _ v u
      apply (rule fresh_cases[of "IImsupp f" u])
       apply (simp only: IImsupp_SSupp_bound assms)
      subgoal for y
        apply (drule spec2[of _ y g])
        apply (auto simp: bij_inv_rev map_TT_cctor supp_id_bound supp_inv_bound F_set_map assms
            intro!: FFVars_intros(2))
        done
      done
    done
  subgoal for fx t a x g
    apply (cases "isVVr (cctor x)")
     apply (drule sym[of "cctor fx"])
     apply (auto simp only: isVVr_def tvsubst_VVr FFVars_VVr UN_iff bex_simps assms map_TT_VVr
        supp_inv_bound bij_imp_bij_inv) []
     apply (auto simp: VVr_def TT_inject0 F_set_map supp_id_bound \<eta>_set4_F) []
    apply (auto simp: tvsubst_cctor_not_isVVr assms F_set_map supp_id_bound supp_inv_bound imsupp_supp_bound
        TT_inject0 map_TT_cctor FFVars_map_TT)
    apply (frule arg_cong[of _ _ set2_F])
    apply (drule arg_cong[of _ _ set4_F])
    apply (auto simp: tvsubst_cctor_not_isVVr assms F_set_map supp_id_bound supp_inv_bound imsupp_supp_bound
        TT_inject0 map_TT_cctor FFVars_map_TT)
    subgoal for b h
      apply (drule id_onD[of _ h a])
       apply auto []
      apply (drule arg_cong[of "h ` _" _ "image (inv h)"])
      apply (drule arg_cong[of "map_TT h ` _" _ "image (map_TT (inv h))"])
      apply (auto simp: image_image map_TT_comp[symmetric] map_TT_id supp_inv_bound
          FFVars_map_TT)
      subgoal for u
        apply (rule fresh_cases[of "IImsupp f" u])
         apply (simp only: IImsupp_SSupp_bound assms)
        subgoal for y
          apply (drule spec2[of _ y "g o h"])
          apply (simp only: supp_comp_bound bij_comp simp_thms map_TT_cctor
              o_inv_distrib supp_inv_bound bij_imp_bij_inv o_apply[of g h a])
          apply (cases "b \<in> set2_F x")
           apply (auto simp: F_set_map supp_id_bound FFVars_VVr
              dest!: IImsupp_empty_IntD2[of "set2_F x"]) []
           apply (metis image_iff inv_simp1)
          apply (rule FFVars_intros(3)[of "tvsubst f (cctor y)"])
           apply (auto simp: F_set_map supp_id_bound)
          done
        done
      done
    done
  done

(* fresnness versus vsubst: *)
theorem FFVars_tvsubst:
  fixes t :: "('a::vvar_TT)TT"
  assumes supp: "|SSupp f| <o bound(any::'a)"
  shows "FFVars (tvsubst f t) = (\<Union>a1 \<in> FFVars t. FFVars (f a1))"
    using IImsupp_SSupp_bound[THEN iffD2, OF supp]
proof (cases rule: fresh_cases[of _ t])
  case (1 x)
  show ?thesis
    unfolding \<open>t = cctor x\<close>
    apply (rule set_eqI iffI)+
     apply (erule FFVars_tvsubst_le[rule_format, OF _ refl, of _ f x];
        simp only: supp imsupp_supp_bound 1)
    apply (erule UN_E)
    apply (rule FFVars_vvsubst_ge[rule_format, of f _ t id, THEN set_mp])
           apply (auto simp: 1 supp_id_bound supp map_TT_id)
    done
qed

theorem tvsubst_VVr_func: "tvsubst VVr t = t"
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (cases "isVVr t")
    subgoal
      apply (auto simp only: tvsubst_VVr SSupp_VVr_bound isVVr_def)
      apply (auto simp only: VVr_def intro!: F.rel_refl)
      done
    subgoal
      apply (rule fresh_cases[of "IImsupp VVr", of t])
       apply (auto simp only: emp_bound tvsubst_cctor_not_isVVr SSupp_VVr_bound simp_thms
          IImsupp_SSupp_bound)
      apply (rule exI conjI refl)+
      apply (auto simp only: F_rel_map bij_id supp_id_bound id_o Grp_def intro!: F.rel_refl)
      done
    done
  done

(* Monadic composition for substitution functions: *)
definition cmp :: "('a::vvar_TT \<Rightarrow> 'a TT) \<Rightarrow> ('a \<Rightarrow> 'a TT) \<Rightarrow> 'a \<Rightarrow> 'a TT" where
  "cmp g f a \<equiv> tvsubst g (f a)"

lemma isVVr_map:
  fixes f g ::"'a::vvar_TT \<Rightarrow> 'a"
  assumes f: "bij f" "|supp f| <o bound(any::'a)" "bij g" "|supp g| <o bound(any::'a)"
  shows "isVVr (cctor (map_F f g h i x)) \<longleftrightarrow> isVVr (cctor x)"
  unfolding isVVr_def VVr_def TT_inject
  apply(auto simp only: supp_id_bound bij_id assms)
  subgoal premises prems for a u
    apply (rule exI[of _ "inv f a"])
    apply (rule exI[of _ id])
    apply (insert \<eta>_set2_F[of a] \<eta>_set3_F[of a] \<eta>_set4_F[of a])
    apply (subst (asm) prems(4)[symmetric])+
    apply (auto simp only: prems(4)[symmetric] prems(1,2,3)
      F_set_map assms id_o inv_o_simp1
      bij_id supp_id_bound bij_imp_bij_inv supp_inv_bound bij_comp supp_comp_bound
      vvsubst_id[abs_def] id_def[symmetric] F.map_id F_map_comp[symmetric]
      intro!: trans[rotated, OF  map_F_\<eta>[of "inv f" id id id a]]
        trans[OF F.map_id[symmetric] F_map_cong])
    done
  subgoal premises prems for a u
    apply (rule exI[of _ "f a"])
    apply (rule exI[of _ id])
    apply (insert \<eta>_set2_F[of a] \<eta>_set3_F[of a] \<eta>_set4_F[of a])
    apply (subst (asm) prems(4)[symmetric])+
    apply (auto simp only: prems(4)[symmetric] prems(1,2,3)
      F_set_map assms o_id inv_o_simp1
      bij_id supp_id_bound bij_imp_bij_inv supp_inv_bound bij_comp supp_comp_bound
      vvsubst_id[abs_def] id_def[symmetric] F.map_id F_map_comp[symmetric]
      intro!: trans[rotated, OF  map_F_\<eta>[of "f" id id id a]]
        F_map_cong)
    done
  done

lemma SSupp_cmp:
  fixes g f :: "('a::vvar_TT) \<Rightarrow> 'a TT"
  assumes SSupp: "|SSupp g| <o bound(any::'a)"
  shows "SSupp (cmp g f) \<subseteq> SSupp g \<union> SSupp f"
  unfolding SSupp_def cmp_def by (auto simp add: assms tvsubst_VVr)

lemma SSupp_comp:
  fixes g :: "('a::vvar_TT) \<Rightarrow> 'a TT"
  assumes SSupp: "|SSupp g| <o bound(any::'a)"
  shows "SSupp (g o f) \<subseteq> SSupp g \<union> supp f"
  unfolding SSupp_def cmp_def by (auto simp add: assms supp_def)

lemma SSupp_cmp_bound:
  fixes g f :: "('a::vvar_TT) \<Rightarrow> 'a TT"
  assumes SSupp: "|SSupp g| <o bound(any::'a)" and "|SSupp f| <o bound(any::'a)"
  shows "|SSupp (cmp g f)| <o bound(any::'a)"
  by (meson assms SSupp_cmp Un_bound card_of_mono1 ordLeq_ordLess_trans)

lemma IImsupp_cmp:
  fixes g f :: "('a::vvar_TT) \<Rightarrow> 'a TT"
  assumes SSupp: "|SSupp g| <o bound(any::'a)"
  shows "IImsupp (cmp g f) \<subseteq> IImsupp g \<union> IImsupp f"
  unfolding IImsupp_def using SSupp_cmp[OF assms, of f]
  apply (auto simp: FFVars_tvsubst[OF assms, of "(f _)", folded cmp_def])
  by (metis (mono_tags, lifting)
      FFVars_VVr SSupp SSupp_def cmp_def empty_iff insert_iff mem_Collect_eq tvsubst_VVr)

(* Compositionality of tvsubst: *)
theorem tvsubst_cmp:
  fixes t :: "('a::vvar_TT)TT"
  assumes SSupp: "|SSupp g| <o bound(any::'a)" "|SSupp f| <o bound(any::'a)"
  shows "tvsubst (cmp g f) t = tvsubst g (tvsubst f t)"
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (cases "isVVr t")
    subgoal
      apply (rule exI[of _ x])+
      apply (auto simp only: isVVr_def tvsubst_VVr assms
         SSupp_cmp_bound cmp_def intro!: F.rel_refl_strong)
      done
    subgoal
      apply (rule fresh_cases[of "IImsupp (cmp g f) \<union> IImsupp f \<union> IImsupp g" t])
       apply (auto simp only: Un_bound IImsupp_SSupp_bound SSupp_cmp_bound
         assms tvsubst_cctor_not_isVVr Int_Un_distrib simp_thms
         F_set_map image_id id_apply supp_id_bound bij_id isVVr_map)
      apply (rule exI conjI refl)+
      apply (auto simp only: F_rel_map F_map_comp[symmetric]
          assms bij_id supp_id_bound supp_comp_bound id_o inv_id)
      apply (rule F.rel_refl_strong)
       apply (auto simp only: o_apply Grp_def)
      done
    done
  done

(* Obliviousness of tvsubst w.r.t. fresh variables: *)
theorem tvsubst_cong:
  fixes t :: "('a::vvar_TT)TT"
  assumes SSupp: "|SSupp f| <o bound(any::'a)" "|SSupp g| <o bound(any::'a)"
    and fr: "\<And> a. a \<in> FFVars t \<Longrightarrow> f a = g a"
  shows "tvsubst f t = tvsubst g t"
  using fr
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (cases "isVVr t")
    subgoal
      apply (rule exI[of _ x])+
      apply (auto simp only: isVVr_def FFVars_VVr insert_iff empty_iff simp_thms tvsubst_VVr assms
          intro!: F.rel_refl_strong)
      done
    subgoal
      apply (rule fresh_cases[of "IImsupp f \<union> IImsupp g" t])
       apply (auto simp only: Un_bound IImsupp_SSupp_bound assms tvsubst_cctor_not_isVVr Int_Un_distrib simp_thms)
      apply (rule exI conjI refl)+
      apply (auto simp only: F_rel_map F_map_comp[symmetric]
          assms bij_id supp_id_bound supp_comp_bound id_o inv_id)
      apply (rule F.rel_refl_strong)
       apply (auto simp only: o_apply id_apply id_def[symmetric] supp_comp_bound supp_id_bound bij_id
          assms F_set_map FFVars_simps relcompp_apply id_o Un_iff UN_iff imp_disjL all_conj_distrib conversep_iff)
      subgoal
        apply (simp only: Grp_def simp_thms UNIV_I)
        apply (rule disjI1 exI conjI refl)+
         apply (auto simp only:)
        done
      subgoal
        apply (simp only: Grp_def simp_thms UNIV_I)
        apply (rule disjI1 exI conjI refl)+
         apply (auto simp only: dest!: IImsupp_empty_IntD1)
        done
      done
    done
  done

theorem tvsubst_cong_id:
  fixes t :: "('a::vvar_TT)TT"
  assumes "|SSupp f| <o bound(any::'a)" "\<And>a. a \<in> FFVars t \<Longrightarrow> f a = VVr a"
  shows "tvsubst f t = t"
  apply (rule trans[OF tvsubst_cong tvsubst_VVr_func])
    apply (simp_all only: assms SSupp_VVr_bound)
  done

lemma SSupp_upd_bound:
  fixes f::"'a::vvar_TT \<Rightarrow> 'a TT"
  shows "|SSupp (f (a:=t))| <o bound(any::'a) \<longleftrightarrow> |SSupp f| <o bound(any::'a)"
  unfolding SSupp_def
  apply (auto simp only: fun_upd_apply singl_bound ordLeq_refl split: if_splits
    elim!: ordLeq_ordLess_trans[OF card_of_mono1 ordLess_ordLeq_trans[OF Un_bound], rotated]
    intro: card_of_mono1)
  done

(* vvsubst vs. term-subst specific infrastructure: *)
theorem vvsubst_VVr:
  fixes f::"'a::vvar_TT \<Rightarrow> 'a"
  assumes "|supp f| <o bound(any::'a)"
  shows "vvsubst f (VVr a) = VVr (f a)"
  unfolding VVr_def using assms
  by (simp add: \<eta>_set2_F \<eta>_set3_F \<eta>_set4_F vvsubst_cctor map_F_\<eta> supp_id_bound)

theorem tvsubst_VVr_vvsubst:
  fixes t :: "('a::vvar_TT)TT"
  assumes f: "|supp f| <o bound(any::'a)"
  shows "tvsubst (VVr o f) t = vvsubst f t"
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (cases "isVVr t")
    subgoal
      apply (auto simp only: tvsubst_VVr vvsubst_VVr SSupp_VVr_bound SSupp_cmp_bound isVVr_def f SSupp_comp_bound o_apply)
      apply (auto simp only: VVr_def intro!: F.rel_refl)
      done
    subgoal
      apply (rule fresh_cases[of "IImsupp (VVr o f) \<union> imsupp f", of t])
       apply (auto simp only: emp_bound tvsubst_cctor_not_isVVr SSupp_VVr_bound simp_thms
          imsupp_supp_bound IImsupp_SSupp_bound SSupp_comp_bound f vvsubst_cctor Un_bound Int_Un_distrib)
      apply (rule exI conjI refl)+
      apply (auto simp only: F_rel_map bij_id supp_id_bound)
      apply (rule F_rel_mono_strong0[rotated 6, OF F_rel_map_right[rotated 6, OF F.rel_refl[of "(=)" "(=)"]]])
                       apply (auto simp only: F_set_map Grp_def f supp_id_bound bij_id o_apply id_apply o_id dest: not_isVVr_set1_F)
      done
    done
  done

(* Unary substitution: *)
definition tusubst :: "('a::vvar_TT) \<Rightarrow> 'a TT \<Rightarrow> 'a TT \<Rightarrow> 'a TT" where
  (* a subsituted by s in t  *)
  "tusubst a s t \<equiv> tvsubst (VVr(a:=s)) t"

(* The next two are simplification rules working with the variable convention: *)
theorem tusubst_cctor_not_isVVr:
  assumes "\<not> isVVr (cctor x)"
    and "a \<notin> set2_F x" " set2_F x \<inter> FFVars s = {}"
  shows "tusubst a s (cctor x) = cctor (map_F id id (tusubst a s) (tusubst a s) x)"
  unfolding tusubst_def
  apply(rule tvsubst_cctor_not_isVVr)
    apply (simp only: SSupp_upd_bound SSupp_VVr_bound)
  using assms
   apply (auto simp only:  fun_upd_apply IImsupp_def SSupp_def
      split: if_splits)
  done

theorem tusubst_VVr:
  fixes a::"'a::vvar_TT"
  shows "tusubst a1 s1 (VVr a) = (if a = a1 then s1 else VVr a)"
  unfolding tusubst_def
  apply (rule trans[OF tvsubst_VVr])
   apply (auto simp only: SSupp_upd_bound SSupp_VVr_bound fun_upd_apply)
  done

theorem FFVars_tusubst:
  fixes t :: "('a::vvar_TT)TT"
  shows "FFVars (tusubst a1 t1 t) = (if a1 \<in> FFVars t then FFVars t - {a1} \<union> FFVars t1 else FFVars t)"
  unfolding tusubst_def
  apply (rule trans[OF FFVars_tvsubst])
   apply (auto simp only: SSupp_upd_bound SSupp_VVr_bound FFVars_VVr fun_upd_apply split: if_splits)
  done

theorem tusubst_cmp_same:
  fixes t :: "('a::vvar_TT)TT"
  shows "tusubst a s2 (tusubst a s1 t) = tusubst a (tusubst a s2 s1) t"
  unfolding tusubst_def
  apply (rule trans[OF tvsubst_cmp[symmetric]])
      apply (auto simp only: SSupp_upd_bound SSupp_VVr_bound cmp_def fun_upd_apply tvsubst_VVr
        intro!: tvsubst_cong SSupp_cmp_bound split: if_splits)
  done

theorem tusubst_cmp_diff:
  fixes t :: "('a::vvar_TT)TT"
  assumes "a1 \<noteq> a2" "a1 \<notin> FFVars s2"
  shows "tusubst a2 s2 (tusubst a1 s1 t) = tusubst a1 (tusubst a2 s2 s1) (tusubst a2 s2 t)"
  using assms unfolding tusubst_def
  apply (intro box_equals[OF _ tvsubst_cmp tvsubst_cmp])
      apply (auto simp only: SSupp_upd_bound SSupp_VVr_bound SSupp_cmp_bound cmp_def fun_upd_apply tvsubst_VVr
        intro!: tvsubst_cong SSupp_cmp_bound tvsubst_cong_id[symmetric] split: if_splits)
  done

theorem tusubst_VVr_same:
  fixes t :: "('a::vvar_TT)TT"
  shows "tusubst a (VVr a) t = t"
  unfolding tusubst_def
  apply (rule tvsubst_cong_id)
   apply (auto simp only: SSupp_VVr_bound SSupp_upd_bound fun_upd_apply split: if_split)
  done

theorem tusubst_idle:
  fixes t :: "('a::vvar_TT)TT"
  assumes "a \<notin> FFVars t"
  shows "tusubst a s t = t"
  unfolding tusubst_def
  apply (rule tvsubst_cong_id)
   apply (auto simp only: SSupp_VVr_bound SSupp_upd_bound fun_upd_apply assms split: if_split)
  done

(* vusubst vs. the term-subst specific infrastructure: *)

theorem vusubst_VVr: "vusubst (a::'a::vvar_TT) (a'::'a::vvar_TT) (VVr a'') = VVr ((id(a:=a')) a'')"
  unfolding vusubst_def
  apply (rule vvsubst_VVr)
   apply (simp_all only: supp_id_upd)
  done
 
theorem tusubst_VVr_vusubst:
  fixes t :: "('a::vvar_TT)TT"
  shows "tusubst a (VVr a') t = vusubst a a' t"
  unfolding tusubst_def vusubst_def
  apply (rule trans[OF _ tvsubst_VVr_vvsubst])
   apply (simp_all only: supp_id_upd fun_upd_comp o_id)
  done

end
