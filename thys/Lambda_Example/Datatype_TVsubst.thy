theory Datatype_TVsubst
  imports Datatype_VVsubst 
begin

(* Replace abstract \<eta> and its assumptions with concrete \<eta>: *) 
(* consts \<eta> :: "'a::var_TT \<Rightarrow> ('a, 'b, 'c, 'd) F" *)

definition \<eta> :: "'a::var_TT \<Rightarrow> ('a, 'b, 'c, 'd) F" where 
"\<eta> \<equiv> C1"

lemma 
  \<eta>_set1_F: "\<And>a. set1_F (\<eta> a) = {a}"
  and
  \<eta>_inj: "\<And> a1 a2. \<eta> a1 = \<eta> a2 \<Longrightarrow> a1 = a2"
  and
  \<eta>_compl_set1_F: "\<And> x. x \<notin> range \<eta> \<Longrightarrow> set1_F x = {}"
  and
  \<eta>_natural: "\<And> (f::'a::var_TT \<Rightarrow> 'a) (g::'b::var_TT \<Rightarrow> 'b) h i. |supp f| <o bound(any::'a) \<Longrightarrow> bij g \<Longrightarrow> |supp g| <o bound(any::'b) \<Longrightarrow> map_F f g h i o \<eta> = \<eta> o f"
unfolding \<eta>_def using LIVE_F.set_cases(1) by force+


(* Immediately satisfied if ('a,'b) F has the form 'a + 'b G *)
lemma map_F_\<eta>:
  "|supp f| <o bound(any::'a) \<Longrightarrow> bij g \<Longrightarrow> |supp g| <o bound(any::'b) \<Longrightarrow>
   map_F  (f::'a::var_TT \<Rightarrow> 'a) (g::'b::var_TT \<Rightarrow> 'b) i j (\<eta> x) = \<eta> (f x)"
  using \<eta>_natural[of f g] unfolding fun_eq_iff by auto

lemma supp_swap_bound: "|supp (id (x := y, y := x :: 'a))| <o bound(any :: 'a :: var_TT)"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF supp_swap_le] finite_ordLess_infinite2])
    (auto simp: var_TT_infinite)


lemma \<eta>_set2_F:
  fixes a :: "'a::var_TT"
  shows "set2_F (\<eta> a :: ('a :: var_TT, 'b :: var_TT, 'c, 'd) F) = {}"
proof -
  { fix b :: 'b
    assume "b \<in> set2_F (\<eta> a :: ('a :: var_TT, 'b :: var_TT, 'c, 'd) F)"
    then have "c \<in> set2_F ((\<eta> o id) a :: ('a :: var_TT, 'b :: var_TT, 'c, 'd) F)" for c
      by (subst \<eta>_natural[symmetric, of id "id(b:=c,c:=b) :: _ \<Rightarrow> _ :: var_TT" id id])
        (auto 0 1 simp only: F_set2_map image_iff supp_id_bound bij_swap supp_swap_bound o_apply
          fun_upd_apply id_apply intro: supp_id_bound supp_swap_bound split: if_splits)
    then have "set2_F (\<eta> a :: ('a :: var_TT, 'b :: var_TT, 'c, 'd) F) = (UNIV :: 'b set)"
      by auto
    then have False
      by (metis F_set2_bd not_ordLess_ordLeq var_TT)
  }
  then show ?thesis by blast
qed

lemma \<eta>_set3_F:
  fixes a :: "'a::var_TT"
  shows "set3_F (\<eta> a :: ('a :: var_TT, 'b :: var_TT, 'c, 'd) F) = {}"
proof -
  { fix b :: 'c
    assume "b \<in> set3_F (\<eta> a :: ('a :: var_TT, 'b :: var_TT, 'c, 'd) F)"
    then have "c \<in> set3_F ((\<eta> o id) a :: ('a :: var_TT, 'b :: var_TT, bd_type_TT set, 'd) F)" for c
      by (subst \<eta>_natural[symmetric, of id "id :: _ \<Rightarrow> _ :: var_TT" "\<lambda>_. c" id])
        (auto simp add: F_set3_map image_iff supp_id_bound intro!: supp_id_bound)
    then have *: "set3_F (\<eta> a :: ('a :: var_TT, 'b :: var_TT, bd_type_TT set, 'd) F) = (UNIV :: bd_type_TT set set)"
      by auto
    have "bd_TT <o |set3_F (\<eta> a :: ('a :: var_TT, 'b :: var_TT, bd_type_TT set, 'd) F) :: bd_type_TT set set|"
      unfolding * using Card_order_Pow F.bd_card_order card_order_on_Card_order by force
    with F.set_bd[of "\<eta> a"] have False
      using not_ordLeq_ordLess by blast
  }
  then show ?thesis by blast
qed

lemma \<eta>_set4_F:
  fixes a :: "'a::var_TT"
  shows "set4_F (\<eta> a :: ('a :: var_TT, 'b :: var_TT, 'c, 'd) F) = {}"
proof -
  { fix b :: 'd
    assume "b \<in> set4_F (\<eta> a :: ('a :: var_TT, 'b :: var_TT, 'c, 'd) F)"
    then have "c \<in> set4_F ((\<eta> o id) a :: ('a :: var_TT, 'b :: var_TT, 'c, bd_type_TT set) F)" for c
      by (subst \<eta>_natural[symmetric, of id "id :: _ \<Rightarrow> _ :: var_TT" id "\<lambda>_. c"])
        (auto simp add: F_set4_map image_iff supp_id_bound intro!: supp_id_bound)
    then have *: "set4_F (\<eta> a :: ('a :: var_TT, 'b :: var_TT, 'c, bd_type_TT set) F) = (UNIV :: bd_type_TT set set)"
      by auto
    have "bd_TT <o |set4_F (\<eta> a :: ('a :: var_TT, 'b :: var_TT, 'c, bd_type_TT set) F) :: bd_type_TT set set|"
      unfolding * using Card_order_Pow F.bd_card_order card_order_on_Card_order by force
    with F.set_bd[of "\<eta> a"] have False
      using not_ordLeq_ordLess by blast
  }
  then show ?thesis by blast
qed


lemma \<eta>_transfer[folded rel_F_id_def, transfer_rule]:
  "rel_fun (=) (rel_F (id :: 'a::var_TT\<Rightarrow>'a) (id :: 'a::var_TT\<Rightarrow>'a) R S) \<eta> \<eta>"
  unfolding rel_fun_def F_rel_map_set2[OF supp_id_bound bij_id supp_id_bound]
  apply safe
  subgoal for _ x
    apply (rule exI[of _ "map_F id id _ _ (\<eta> x)"])
    apply (unfold F.set_map F.map_comp)
    apply (subst map_F_\<eta>; auto simp: \<eta>_set3_F \<eta>_set4_F supp_id card_of_empty4)+
    done
  done

definition VVr :: "'a::var_TT \<Rightarrow> 'a TT" where "VVr a \<equiv> cctor (\<eta> a)"

lemma VVr_inj: "VVr a1 = VVr a2 \<longleftrightarrow> a1 = a2"
  unfolding VVr_def by (auto simp add: \<eta>_inj TT_inject map_F_\<eta> supp_id_bound)

definition isVVr :: "'a::var_TT TT \<Rightarrow> bool" where
  "isVVr t \<equiv> (\<exists>a. t = VVr a)"

definition asVVr :: "'a::var_TT TT \<Rightarrow> 'a" where
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

lemma map_TT_VVr: "bij (g::'a::var_TT\<Rightarrow>'a) \<Longrightarrow> |supp g| <o bound(any::'a) \<Longrightarrow> map_TT g (VVr a) = VVr (g a)"
  unfolding VVr_def by (auto simp: \<eta>_natural[unfolded o_def fun_eq_iff, rule_format] map_TT_cctor)

(***************************************)
(* Substitution of terms for variables  *)
(***************************************)

(* The Support of a substitution function f: *)
definition SSupp :: "('a::var_TT \<Rightarrow> 'a TT) \<Rightarrow> 'a set" where
  "SSupp f \<equiv> {a . f a \<noteq> VVr a}"

(* The Support of f factoring in the image too: *)
definition IImsupp :: "('a::var_TT \<Rightarrow> 'a TT) \<Rightarrow> 'a set" where
  "IImsupp f \<equiv> SSupp f \<union> (\<Union> a \<in> SSupp f. FFVars (f a))"

lemma SSupp_VVr_bound: "|SSupp VVr| <o bound(any::'a::var_TT)"
  unfolding SSupp_def by (auto simp: emp_bound)


lemma IImsupp_SSupp_bound:
  "|IImsupp (g::'a::var_TT\<Rightarrow>'a TT)| <o bound(any::'a) \<longleftrightarrow> |SSupp g| <o bound(any::'a)"
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
  fixes f :: "'a::var_TT\<Rightarrow>'a TT" and g :: "'a::var_TT\<Rightarrow>'a"
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
  fixes t :: "'a::var_TT TT"
  obtains a where "t = VVr a" | "\<not> isVVr t"
  by (metis isVVr_asVVr)

typedef 'a :: var_TT SSfun = "{f :: 'a \<Rightarrow> 'a TT. |SSupp f| <o bound(any :: 'a)}"
  by (auto intro!: exI[of _ VVr] simp: SSupp_VVr_bound)

lemma map_TT_eq_VVr_iff:
  "bij (f :: 'a \<Rightarrow> 'a :: var_TT) \<Longrightarrow> |supp f| <o bound(any :: 'a) \<Longrightarrow>
    map_TT f x = VVr y \<longleftrightarrow> (\<exists>z. x = VVr z \<and> y = f z)"
  by (cases x)
    (auto simp: VVr_inj map_TT_VVr map_TT_comp[symmetric] supp_inv_bound map_TT_id
      dest!: arg_cong[of "map_TT f x" _ "map_TT (inv f)"])

lemma SSupp_comp_le:
  fixes u :: "'a \<Rightarrow> 'a :: var_TT" and f :: "'a \<Rightarrow> 'a TT"
  assumes u: "bij u" "|supp u| <o bound (any :: 'a)"
  shows "SSupp (map_TT u o f) \<subseteq> SSupp f \<union> supp u"
  unfolding SSupp_def supp_def
  by (auto simp: map_TT_VVr assms)

lemma SSupp_comp_le2:
  fixes u :: "'a \<Rightarrow> 'a :: var_TT" and f :: "'a \<Rightarrow> 'a TT"
  assumes u: "bij u" "|supp u| <o bound (any :: 'a)"
  shows "SSupp (f o u) \<subseteq> SSupp f \<union> supp u"
  unfolding SSupp_def supp_def
  by (auto simp: map_TT_VVr assms)

lemma SSupp_comp_bound:
  fixes u :: "'a \<Rightarrow> 'a :: var_TT" and f :: "'a \<Rightarrow> 'a TT"
  assumes u: "bij u" "|supp u| <o bound (any :: 'a)" and f: "|SSupp f| <o bound (any :: 'a)"
  shows "|SSupp (map_TT u o f)| <o bound (any :: 'a)"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_comp_le]])
    (auto simp: assms Un_bound)

lemma SSupp_comp_bound2:
  fixes u :: "'a \<Rightarrow> 'a :: var_TT" and f :: "'a \<Rightarrow> 'a TT"
  assumes u: "bij u" "|supp u| <o bound (any :: 'a)" and f: "|SSupp f| <o bound (any :: 'a)"
  shows "|SSupp (f o u)| <o bound (any :: 'a)"
  by (rule ordLeq_ordLess_trans[OF card_of_mono1[OF SSupp_comp_le2]])
    (auto simp: assms Un_bound)

setup_lifting type_definition_SSfun

lift_definition vvrSS :: "'a :: var_TT SSfun" is VVr
  by (simp add: SSupp_VVr_bound)

context
  fixes u :: "'a :: var_TT \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o bound(any :: 'a)"
begin

lift_definition compSS :: "'a :: var_TT SSfun \<Rightarrow> 'a SSfun" is "\<lambda>p. map_TT u o p o inv u"
  by (auto simp: u supp_inv_bound SSupp_comp_bound SSupp_comp_bound2)

end

context
  fixes u :: "'a :: var_TT \<Rightarrow> 'a"
  assumes u[transfer_rule, simp]: "bij u" "|supp u| <o bound(any :: 'a)"
begin

lemma compSS_inv_compSS[simp]: "compSS (inv u) (compSS u p) = p"
  supply bij_imp_bij_inv[transfer_rule] supp_inv_bound[transfer_rule]
  apply transfer
  apply (auto simp: o_def map_TT_comp[symmetric] supp_inv_bound id_def[symmetric] map_TT_id)
  done

end

lemma compSS_id[simp]: "compSS id = id"
  supply supp_id_bound[transfer_rule] bij_id[transfer_rule]
  by (rule ext, transfer) (auto simp: map_TT_id)

template_instance VVSUBST: REC where
  'a REC.P = "'a SSfun" and 'a REC.C = "'a TT"
for
  "REC.A :: 'a::var_TT set"
  = "{} :: 'a::var_TT set"
  and
  "REC.CCTOR :: ('a::var_TT, 'a, 'a TT \<times> ('a REC.P \<Rightarrow> 'a REC.C), 'a TT \<times> ('a REC.P \<Rightarrow> 'a REC.C)) F \<Rightarrow> 'a REC.P \<Rightarrow> 'a REC.C"
  = "(\<lambda>F p. if isVVr (cctor (map_F id id fst fst F)) then
       Rep_SSfun p (asVVr (cctor (map_F id id fst fst F)))
     else
       cctor (map_F id id ((\<lambda>R. R p) o snd) ((\<lambda>R. R p) o snd) F)) ::
  ('a::var_TT, 'a, 'a TT \<times> (('a SSfun) \<Rightarrow> 'a TT), 'a TT \<times> (('a SSfun) \<Rightarrow> 'a TT)) F \<Rightarrow> ('a SSfun) \<Rightarrow> 'a TT"
  and
  "REC.mmapC :: ('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a TT \<Rightarrow> 'a REC.C \<Rightarrow> 'a REC.C"
  = "(\<lambda>f _ x. map_TT f x) :: ('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a TT \<Rightarrow> 'a TT \<Rightarrow> 'a TT"
  and
  "REC.FFVarsC :: 'a TT \<Rightarrow> 'a::var_TT REC.C \<Rightarrow> 'a set"
  = "(\<lambda>_ x. FFVars x) :: 'a TT \<Rightarrow> 'a::var_TT TT \<Rightarrow> 'a set"
  and
  "REC.mapP :: ('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a REC.P \<Rightarrow> 'a REC.P"
  = "(\<lambda>u p. compSS u p) :: ('a::var_TT \<Rightarrow> 'a) \<Rightarrow> ('a SSfun) \<Rightarrow> ('a SSfun)"
  and
  "REC.FVarsP :: 'a::var_TT REC.P \<Rightarrow> 'a set"
  = "(\<lambda>p. IImsupp (Rep_SSfun p)) :: ('a::var_TT SSfun) \<Rightarrow> 'a set"
       apply -
  subgoal by (rule emp_bound)
  subgoal
    using emp_bound IImsupp_SSupp_bound Rep_SSfun by auto 
  subgoal unfolding termLikeStr_def apply safe
    subgoal by simp
    subgoal premises prems for u v
      supply prems[transfer_rule] bij_comp[transfer_rule] supp_comp_bound[transfer_rule]
      by (rule ext, transfer fixing: u v) (auto simp: fun_eq_iff prems o_inv_distrib map_TT_comp[symmetric])
    subgoal premises prems for u p
      supply prems(1,2)[transfer_rule]
      using prems(3)
      apply (transfer fixing: u)
      subgoal for p
        unfolding fun_eq_iff o_apply
        apply (subst IImsupp_imsupp_map_TT_commute[of p u, OF _ prems(1,2)])
         apply (auto simp: prems(1) image_iff imsupp_def supp_def)
        done
      done
    subgoal premises prems for u p a
      supply prems(1,2)[transfer_rule]
      using prems(3)
      apply (transfer fixing: u a)
      subgoal for p
        apply (force simp: IImsupp_def SSupp_def prems(1,2) map_TT_VVr
            map_TT_eq_VVr_iff FFVars_map_TT)
        done
      done
    subgoal premises prems for u p a
      supply prems(1,2)[transfer_rule]
      using prems(3)
      apply (transfer fixing: u a)
      subgoal for p
        apply (auto simp: IImsupp_def SSupp_def prems(1,2) map_TT_VVr
            map_TT_eq_VVr_iff FFVars_map_TT image_iff FFVars_VVr dest!: spec[of _ "u _"])
        done
      done
    done
  subgoal
    apply (cases "isVVr (cctor (map_F id id fst fst X))")
    subgoal
      apply (erule thin_rl)
      apply (auto simp: isVVr_def FFVars_VVr asVVr_VVr IImsupp_def SSupp_def)
      apply (metis FFVars_VVr emptyE insertE)
      done
    subgoal apply (auto simp: IImsupp_SSupp_bound
          FFVars_simps F_set_map supp_id_bound emp_bound Rep_SSfun[simplified])
        apply (metis (no_types, hide_lams) UnE fst_conv subset_eq)
       apply (metis (no_types, hide_lams) UnE fst_conv subset_eq)
      apply (metis (no_types, hide_lams) UnE fst_conv subset_eq)
      done
    done
  subgoal
    apply (cases "isVVr (cctor (map_F id id fst fst X))")
    subgoal
      apply (auto 4 4 simp: isVVr_def F_map_comp[symmetric] supp_id_bound supp_inv_bound
          asVVr_VVr IImsupp_def SSupp_def compSS.rep_eq o_def split_beta map_TT_cctor
          id_def[symmetric] map_TT_comp[symmetric] map_TT_VVr VVr_inj
          dest: arg_cong[of _ "VVr _" "map_TT u"])
      done
    subgoal
      apply (auto simp: isVVr_def)
       apply (auto simp: map_TT_cctor compSS.rep_eq F_map_comp[symmetric] Rep_SSfun[simplified]
          supp_comp_bound supp_inv_bound supp_id_bound mmapfn_def inv_o_simp1[THEN rewriteR_comp_comp]
          map_TT_id map_TT_comp[symmetric] isVVr_def o_def split_beta asVVr_VVr id_def[symmetric] map_TT_VVr
          dest!: arg_cong[of _ "VVr _" "map_TT (inv u)"]
          intro!: cctor_eq_intro_map_TT[of id] F_map_cong)
      done
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
  fixes f :: "'a :: var_TT \<Rightarrow> 'a TT"
  assumes f: "|SSupp f| <o bound (any :: 'a)"
begin

lift_definition fSS :: "'a SSfun" is f by (rule f)

definition tvsubst where "tvsubst x = ff0 x fSS"

lemma tvsubst_VVr: "tvsubst (VVr x) = f x"
  unfolding tvsubst_def VVr_def
  by (subst ff0_cctor)
    (auto simp: isVVr_def asVVr_VVr VVr_def[symmetric]
      TT_inject F_map_comp[symmetric] supp_id_bound
      \<eta>_set2_F nnoclash_def map_F_\<eta> fSS.rep_eq)

lemma tvsubst_cctor_not_isVVr: "set2_F x \<inter> (IImsupp f) = {} \<Longrightarrow> nnoclash x \<Longrightarrow>
  \<not> isVVr (cctor x) \<Longrightarrow> tvsubst (cctor x) = cctor (map_F id id tvsubst tvsubst x)"
  unfolding tvsubst_def
  by (subst ff0_cctor)
    (auto simp: F_map_comp[symmetric] F.map_id f supp_id_bound o_def id_def[symmetric] Rep_SSfun fSS.rep_eq)

lemma FFVars_vvsubst_weak: "FFVars (tvsubst t) \<subseteq> FFVars t \<union> IImsupp f"
  unfolding tvsubst_def
  by (rule order_trans[OF ff0_FFVars])
    (auto simp: F_map_comp[symmetric] f supp_id_bound o_def id_def[symmetric] Rep_SSfun fSS.rep_eq)

end

thm vvsubst_cctor FFVars_vvsubst_weak

(* fresnness versus vsubst: *)
theorem FFVars_tvsubst:
  fixes t :: "('a::var_TT)TT"
  assumes supp: "|SSupp f| <o bound(any::'a)"
  shows "FFVars (tvsubst f t) = (\<Union>a1 \<in> FFVars t. FFVars (f a1))"
  apply (induct t rule: TT_fresh_induct[consumes 0, of "IImsupp f"])
   apply (simp only: IImsupp_SSupp_bound supp)
  subgoal for x
    apply (cases "isVVr (cctor x)")
    subgoal
      by (auto simp: isVVr_def tvsubst_VVr supp FFVars_VVr)
    subgoal
      apply (subst tvsubst_cctor_not_isVVr)
          apply (auto simp: supp nnoclash_def FFVars_simps F_set_map supp_id_bound image_iff
          not_isVVr_set1_F)
      subgoal for z t a
        apply (cases "f a = VVr a")
         apply (auto simp: FFVars_VVr IImsupp_def SSupp_def dest: bspec[of _ _ a])
        done
      subgoal for z a t
        apply (cases "f a = VVr a")
         apply (auto simp: FFVars_VVr IImsupp_def SSupp_def dest!: meta_spec[of _ z])
        done
      done
    done
  done

theorem tvsubst_VVr_func: "tvsubst VVr t = t"
proof(induction t rule: TT_plain_induct)
  case (cctor x)
  show ?case proof (cases "cctor x")
    case (VVr a)
    thus ?thesis by (simp add: SSupp_VVr_bound tvsubst_VVr)
  next
    case nonVVr
    hence 0: "tvsubst VVr (cctor x) = cctor (map_F id id (tvsubst VVr) (tvsubst VVr) x)"
      using tvsubst_cctor_not_isVVr[OF SSupp_VVr_bound] cctor(3,4)
      by (auto simp: nnoclash_def IImsupp_def FFVars_VVr SSupp_def)
    thus ?thesis using cctor.IH unfolding 0
      by (intro arg_cong[of _ _ cctor])
        (auto simp only: supp_id_bound id_apply
          intro!: trans[OF F_map_cong F_map_id[THEN fun_cong], THEN trans[OF _ id_apply]])
  qed
qed

(* Monadic composition for substitution functions: *)
definition cmp :: "('a::var_TT \<Rightarrow> 'a TT) \<Rightarrow> ('a \<Rightarrow> 'a TT) \<Rightarrow> 'a \<Rightarrow> 'a TT" where
  "cmp g f a \<equiv> tvsubst g (f a)"

lemma isVVr_map:
  fixes f g ::"'a::var_TT \<Rightarrow> 'a"
  assumes f: "bij f" "|supp f| <o bound(any::'a)" "bij g" "|supp g| <o bound(any::'a)"
  shows "isVVr (cctor (map_F f g h i x)) \<longleftrightarrow> isVVr (cctor x)"
  unfolding isVVr_def VVr_def TT_inject0
  apply(auto simp only: supp_id_bound bij_id assms)
  subgoal premises prems for a u
    apply (rule exI[of _ "inv f a"])
    apply (rule exI[of _ id])
    apply (insert \<eta>_set2_F[of a] \<eta>_set3_F[of a] \<eta>_set4_F[of a])
    apply (subst (asm) prems(4)[symmetric])+
    apply (auto simp only: prems(4)[symmetric] prems(1,2,3)
        F_set_map assms id_o inv_o_simp1 map_TT_id
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
        id_o id_def[symmetric] F.map_id F_map_comp[symmetric]
        intro!: trans[rotated, OF  map_F_\<eta>[of "f" id id id a]]
        F_map_cong)
    done
  done

lemma SSupp_cmp:
  fixes g f :: "('a::var_TT) \<Rightarrow> 'a TT"
  assumes SSupp: "|SSupp g| <o bound(any::'a)"
  shows "SSupp (cmp g f) \<subseteq> SSupp g \<union> SSupp f"
  unfolding SSupp_def cmp_def by (auto simp add: assms tvsubst_VVr)

lemma SSupp_cmp_bound:
  fixes g f :: "('a::var_TT) \<Rightarrow> 'a TT"
  assumes SSupp: "|SSupp g| <o bound(any::'a)" and "|SSupp f| <o bound(any::'a)"
  shows "|SSupp (cmp g f)| <o bound(any::'a)"
  by (meson assms SSupp_cmp Un_bound card_of_mono1 ordLeq_ordLess_trans)

lemma IImsupp_cmp:
  fixes g f :: "('a::var_TT) \<Rightarrow> 'a TT"
  assumes SSupp: "|SSupp g| <o bound(any::'a)"
  shows "IImsupp (cmp g f) \<subseteq> IImsupp g \<union> IImsupp f"
  unfolding IImsupp_def using SSupp_cmp[OF assms, of f]
  apply (auto simp: FFVars_tvsubst[OF assms, of "(f _)", folded cmp_def])
  by (metis (mono_tags, lifting)
      FFVars_VVr SSupp SSupp_def cmp_def empty_iff insert_iff mem_Collect_eq tvsubst_VVr)

(* Compositionality of tvsubst: *)
theorem tvsubst_cmp:
  fixes t :: "('a::var_TT)TT"
  assumes SSupp: "|SSupp g| <o bound(any::'a)" "|SSupp f| <o bound(any::'a)"
  shows "tvsubst (cmp g f) t = tvsubst g (tvsubst f t)"
proof-
  let ?A = "IImsupp g \<union> IImsupp f"
  have "|?A| <o bound(any::'a)"
    using SSupp[unfolded IImsupp_SSupp_bound[symmetric]]
      Un_bound bound_Card_order bound_cinfinite by blast
  thus ?thesis proof(induction t)
    case (cctor x)
    show ?case proof (cases "cctor x")
      case (VVr a)
      thus ?thesis using SSupp_cmp_bound assms cmp_def by (fastforce simp: tvsubst_VVr)
    next
      case nonVVr
      define xx where xx: "xx = map_F id id (tvsubst f) (tvsubst f) x"
      with cctor SSupp have "nnoclash xx"
        apply (auto simp: nnoclash_def F_set_map supp_id_bound FFVars_tvsubst)
        subgoal for z t a
          apply (cases "f a = VVr a")
          apply (auto simp: FFVars_VVr IImsupp_def SSupp_def)
          done
        done
      have nnonVVr: "\<not> isVVr (cctor xx)" unfolding xx using nonVVr by (auto simp: isVVr_map supp_id_bound)
      have f: "tvsubst f (cctor x) = cctor xx"
        using nonVVr SSupp cctor unfolding xx apply (intro tvsubst_cctor_not_isVVr) by (auto simp: nnoclash_def)
      have g: "tvsubst g (cctor xx) = cctor (map_F id id (tvsubst g) (tvsubst g) xx)"
        using SSupp cctor nnonVVr \<open>nnoclash xx\<close>
        by (intro tvsubst_cctor_not_isVVr)
          (auto simp: xx F_set_map supp_id_bound FFVars_tvsubst isVVr_map)
      have gf: "tvsubst (cmp g f) (cctor x) =
              cctor (map_F id id (tvsubst (cmp g f)) (tvsubst (cmp g f)) x)"
        using  nonVVr SSupp_cmp_bound[OF SSupp] cctor IImsupp_cmp[OF SSupp(1)]
        by (intro tvsubst_cctor_not_isVVr) (fastforce simp: nnoclash_def)+
          (* nice thing about fresh induction: allows us to work with plain
      equality, i.e., for cctor we don't need BB_swpd_def2, but only arg_cong *)
      show ?thesis unfolding f g gf using cctor.IH
        by (intro arg_cong[of _ _ cctor])
          (auto simp: xx F.map_comp o_def intro!: F.map_cong)
    qed
  qed
qed

(* Obliviousness of tvsubst w.r.t. fresh variables: *)
theorem tvsubst_cong:
  fixes t :: "('a::var_TT)TT"
  assumes SSupp: "|SSupp f| <o bound(any::'a)" "|SSupp g| <o bound(any::'a)"
    and fr: "\<And> a. a \<in> FFVars t \<Longrightarrow> f a = g a"
  shows "tvsubst f t = tvsubst g t"
proof-
  let ?A = "IImsupp f \<union> IImsupp g"
  have "|?A| <o bound(any::'a)"
    using SSupp[unfolded IImsupp_SSupp_bound[symmetric]]
      Un_bound bound_Card_order bound_cinfinite by blast
  thus ?thesis using fr proof(induction t)
    case (cctor x)
    show ?case proof (cases "cctor x")
      case (VVr a)
      thus ?thesis using cctor(6) SSupp by (simp add: FFVars_VVr tvsubst_VVr)
    next
      case nonVVr
      have f: "tvsubst f (cctor x) = cctor (map_F id id (tvsubst f) (tvsubst f) x)"
        using nonVVr SSupp cctor by (intro tvsubst_cctor_not_isVVr) (auto simp: nnoclash_def)
      have g: "tvsubst g (cctor x) = cctor (map_F id id (tvsubst g) (tvsubst g) x)"
        using nonVVr SSupp cctor by (intro tvsubst_cctor_not_isVVr) (auto simp: nnoclash_def)
      show ?thesis unfolding f g using nonVVr
        apply (intro arg_cong[of _ _ cctor])
        apply (auto simp:  F.map_comp intro!: F.map_cong)
        subgoal apply(rule cctor.IH(1)) using cctor.prems by (auto dest: FFVars_intros(2))
        subgoal for b apply(rule cctor.IH(2)) apply auto subgoal for a
          using cctor.prems[of a] cctor.hyps[of a] apply (auto dest!: FFVars_intros(3))
          by (metis (mono_tags, lifting) IImsupp_def SSupp_def UnI1 mem_Collect_eq) . .
  qed
qed
qed

theorem tvsubst_cong_id:
  fixes t :: "('a::var_TT)TT"
  assumes "|SSupp f| <o bound(any::'a)" "\<And>a. a \<in> FFVars t \<Longrightarrow> f a = VVr a"
  shows "tvsubst f t = t"
  apply (rule trans[OF tvsubst_cong tvsubst_VVr_func])
  apply (simp_all only: assms SSupp_VVr_bound)
  done

lemma SSupp_upd_bound:
  fixes f::"'a::var_TT \<Rightarrow> 'a TT"
  shows "|SSupp (f (a:=t))| <o bound(any::'a) \<longleftrightarrow> |SSupp f| <o bound(any::'a)"
  unfolding SSupp_def
  apply (auto simp only: fun_upd_apply singl_bound ordLeq_refl split: if_splits
      elim!: ordLeq_ordLess_trans[OF card_of_mono1 ordLess_ordLeq_trans[OF Un_bound], rotated]
      intro: card_of_mono1)
  done

(* vvsubst vs. term-subst specific infrastructure: *)
theorem vvsubst_VVr:
  fixes f::"'a::var_TT \<Rightarrow> 'a"
  assumes "|supp f| <o bound(any::'a)"
  shows "vvsubst f (VVr a) = VVr (f a)"
  unfolding VVr_def using assms
  by (simp add: \<eta>_set2_F \<eta>_set3_F \<eta>_set4_F vvsubst_cctor nnoclash_def map_F_\<eta> supp_id_bound)

theorem tvsubst_VVr_vvsubst:
  fixes t :: "('a::var_TT)TT"
  assumes f: "|supp f| <o bound(any::'a)"
  shows "tvsubst (VVr o f) t = vvsubst f t"
  using supp_imsupp_bound[OF f] proof(induction t)
  case (cctor x)
  show ?case proof (cases "cctor x")
    case (VVr a)
    have 0: "tvsubst (VVr \<circ> f) (cctor x) = (VVr o f) a"
      unfolding VVr apply(rule tvsubst_VVr) using cctor f by (auto simp: SSupp_def VVr_inj supp_def)
    show ?thesis unfolding 0 using cctor VVr f by (simp add: vvsubst_VVr)
  next
    case nonVVr
    have 0: "tvsubst (VVr \<circ> f) (cctor x) = cctor (map_F id id (tvsubst (VVr \<circ> f)) (tvsubst (VVr \<circ> f)) x)"
      apply(rule tvsubst_cctor_not_isVVr) using cctor using nonVVr f
      apply (auto 7 0 simp: IImsupp_def SSupp_def VVr_inj supp_def imsupp_def image_iff FFVars_VVr nnoclash_def)
      done
    have 1: "vvsubst f (cctor x) = cctor (map_F f id (vvsubst f) (vvsubst f) x)"
      apply(rule vvsubst_cctor) using f cctor(3,4,5) by (auto simp: nnoclash_def)
    show ?thesis unfolding 0 1 apply(rule cong[of _ cctor])
      apply (auto simp: nonVVr not_isVVr_set1_F f supp_id_bound intro!: F_map_cong)
      subgoal by (auto simp: nonVVr  not_isVVr_set1_F f intro!: F_map_cong cctor.IH(1))
      subgoal by (auto simp: nonVVr  not_isVVr_set1_F f intro!: F_map_cong cctor.IH(2)) .
  qed
qed

(* Unary substitution: *)
definition tusubst :: "('a::var_TT) \<Rightarrow> 'a TT \<Rightarrow> 'a TT \<Rightarrow> 'a TT" where
  (* a subsituted by s in t  *)
  "tusubst a s t \<equiv> tvsubst (VVr(a:=s)) t"

(* The next two are simplification rules working with the variable convention: *)
theorem tusubst_cctor_not_isVVr:
  assumes "\<not> isVVr (cctor x)"
    and "a \<notin> set2_F x" " set2_F x \<inter> FFVars s = {}" "nnoclash x"
  shows "tusubst a s (cctor x) = cctor (map_F id id (tusubst a s) (tusubst a s) x)"
  unfolding tusubst_def
  apply(rule tvsubst_cctor_not_isVVr)
  apply (simp only: SSupp_upd_bound SSupp_VVr_bound)
  using assms
  apply (auto simp only:  fun_upd_apply IImsupp_def SSupp_def
      split: if_splits)
  done

theorem tusubst_VVr:
  fixes a::"'a::var_TT"
  shows "tusubst a1 s1 (VVr a) = (if a = a1 then s1 else VVr a)"
  unfolding tusubst_def
  apply (rule trans[OF tvsubst_VVr])
  apply (auto simp only: SSupp_upd_bound SSupp_VVr_bound fun_upd_apply)
  done

theorem FFVars_tusubst:
  fixes t :: "('a::var_TT)TT"
  shows "FFVars (tusubst a1 t1 t) = (if a1 \<in> FFVars t then FFVars t - {a1} \<union> FFVars t1 else FFVars t)"
  unfolding tusubst_def
  apply (rule trans[OF FFVars_tvsubst])
  apply (auto simp only: SSupp_upd_bound SSupp_VVr_bound FFVars_VVr fun_upd_apply split: if_splits)
  done

theorem tusubst_cmp_same:
  fixes t :: "('a::var_TT)TT"
  shows "tusubst a s2 (tusubst a s1 t) = tusubst a (tusubst a s2 s1) t"
  unfolding tusubst_def
  apply (rule trans[OF tvsubst_cmp[symmetric]])
  apply (auto simp only: SSupp_upd_bound SSupp_VVr_bound cmp_def fun_upd_apply tvsubst_VVr
      intro!: tvsubst_cong SSupp_cmp_bound split: if_splits)
  done

theorem tusubst_cmp_diff:
  fixes t :: "('a::var_TT)TT"
  assumes "a1 \<noteq> a2" "a1 \<notin> FFVars s2"
  shows "tusubst a2 s2 (tusubst a1 s1 t) = tusubst a1 (tusubst a2 s2 s1) (tusubst a2 s2 t)"
  using assms unfolding tusubst_def
  apply (intro box_equals[OF _ tvsubst_cmp tvsubst_cmp])
  apply (auto simp only: SSupp_upd_bound SSupp_VVr_bound SSupp_cmp_bound cmp_def fun_upd_apply tvsubst_VVr
      intro!: tvsubst_cong SSupp_cmp_bound tvsubst_cong_id[symmetric] split: if_splits)
  done

theorem tusubst_VVr_same:
  fixes t :: "('a::var_TT)TT"
  shows "tusubst a (VVr a) t = t"
  unfolding tusubst_def
  apply (rule tvsubst_cong_id)
  apply (auto simp only: SSupp_VVr_bound SSupp_upd_bound emp_bound fun_upd_apply split: if_split)
  done

theorem tusubst_idle:
  fixes t :: "('a::var_TT)TT"
  assumes "a \<notin> FFVars t"
  shows "tusubst a s t = t"
  unfolding tusubst_def
  apply (rule tvsubst_cong_id)
  apply (auto simp only: SSupp_VVr_bound SSupp_upd_bound fun_upd_apply assms split: if_split)
  done

(* vusubst vs. the term-subst specific infrastructure: *)

theorem vusubst_VVr: "vusubst (a::'a::var_TT) (a'::'a::var_TT) (VVr a'') = VVr ((id(a:=a')) a'')"
  unfolding vusubst_def
  apply (rule vvsubst_VVr)
  apply (simp_all only: supp_id_upd)
  done

theorem tusubst_VVr_vusubst:
  fixes t :: "('a::var_TT)TT"
  shows "tusubst a (VVr a') t = vusubst a a' t"
  unfolding tusubst_def vusubst_def
  apply (rule trans[OF _ tvsubst_VVr_vvsubst])
  apply (simp_all only: supp_id_upd fun_upd_comp o_id)
  done

end