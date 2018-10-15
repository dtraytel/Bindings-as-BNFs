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

template_instance VVSUBST: COREC where
  'a COREC.D = "'a TT \<times> 'a SSfun"
for
  "COREC.DDTOR :: 'a::vvar_TT COREC.D \<Rightarrow> ('a, 'a, 'a TT + 'a COREC.D, 'a TT + 'a COREC.D) F set"
  = "(\<lambda>(t, f). 
      if isVVr t then {map_F id id Inl Inl x | x. Rep_SSfun f (asVVr t) = cctor x}
      else
      {map_F id id (\<lambda>x. Inr (x, f)) (\<lambda>x. Inr (x, f)) x | x.
        t = cctor x \<and> set2_F x \<inter> IImsupp (Rep_SSfun f) = {}}) :: 
  ('a::vvar_TT TT \<times> 'a SSfun \<Rightarrow> ('a, 'a, 'a TT + 'a TT \<times> 'a SSfun , 'a TT + 'a TT \<times> 'a SSfun) F set)"
  and
  "COREC.mmapD :: ('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'a COREC.D \<Rightarrow> 'a COREC.D"
  = "(\<lambda>u (x, f). (map_TT u x, compSS u f)) :: ('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'a TT \<times> 'a SSfun \<Rightarrow> 'a TT \<times> 'a SSfun"
  and
  "COREC.FFVarsD :: 'a::vvar_TT COREC.D \<Rightarrow> 'a set"
  = "(\<lambda>(x, f). FFVars x \<union> IImsupp (Rep_SSfun f)) :: 'a::vvar_TT TT \<times> 'a SSfun \<Rightarrow> 'a set"
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
    apply clarsimp
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

hide_const f

context
  fixes f :: "'a :: vvar_TT \<Rightarrow> 'a TT"
  assumes f: "|SSupp f| <o bound (any :: 'a)"
begin

lift_definition fSS :: "'a SSfun" is f by (rule f)

definition tvsubst where "tvsubst x = ff0 (x, fSS)"

lemma tvsubst_VVr: "tvsubst (VVr x) = f x"
  unfolding tvsubst_def
  by (subst ff0_DDTOR[of "map_F id id Inl Inl (SOME F. f x = cctor F)"])
    (auto simp add: isVVr_def asVVr_VVr VVr_inj fSS.rep_eq
     F_map_comp[symmetric] supp_id_bound case_sum_o_inj F.map_id
     someI_ex[OF TT_nchotomy[rule_format, of "f x"], symmetric])

lemma tvsubst_cctor_not_isVVr: "set2_F x \<inter> (IImsupp f) = {} \<Longrightarrow>
  \<not> isVVr (cctor x) \<Longrightarrow> tvsubst (cctor x) = cctor (map_F id id tvsubst tvsubst x)"
  unfolding tvsubst_def
  by (subst ff0_DDTOR)
    (auto simp: F_map_comp[symmetric] f supp_id_bound o_def id_def[symmetric] fSS.rep_eq)

lemma FFVars_vvsubst_weak: "FFVars (tvsubst t) \<subseteq> FFVars t \<union> IImsupp f"
  unfolding tvsubst_def
  by (rule order_trans[OF ff0_FFVarsD])
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
  unfolding tvsubst_def[OF f] ff0_mmapD[OF u, symmetric]
  by (auto simp: tvsubst_def assms ff0_mmapD[symmetric] SSupp_comp_bound SSupp_comp_bound2
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
