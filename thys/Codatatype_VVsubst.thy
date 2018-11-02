theory Codatatype_VVsubst
imports More_Codatatype_Bindings
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




(* Term-like structures: *)
definition termLikeStr :: "(('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'a set) \<Rightarrow> bool" where 
  "termLikeStr swp fvars \<equiv>
  swp id = id \<and> 
  (\<forall> u v. bij u \<and> |supp u| <o bound (any::'a) \<and> bij v \<and> |supp v| <o bound (any::'a)
      \<longrightarrow> swp (u o v) = swp u o swp v) \<and> 
  (\<forall> u c. bij u \<and> |supp u| <o bound (any::'a) \<and>
      (\<forall> a. a \<in> fvars c \<longrightarrow> u a = a) \<longrightarrow> swp u c = c) \<and>
  (\<forall> u c a. bij u \<and> |supp u| <o bound (any::'a) 
     \<longrightarrow> (u a \<in> fvars (swp u c) \<longleftrightarrow> a \<in> fvars c))"

(* A restricted version of "termLikeStr" to be used for the comodels -- it only 
assums small-support bijection functoriality and nothing else, 
in particular nothing about freshness.  *)
abbreviation termLikeStrD :: "(('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> bool" where 
  "termLikeStrD swp  \<equiv>
  (\<forall> c. swp id c = c) \<and> 
  (\<forall> u v c. bij u \<and> |supp u| <o bound (any::'a) \<and> bij v \<and> |supp v| <o bound (any::'a)
    \<longrightarrow>  swp (u o v) c = swp u (swp v c))"

(* The following definition and three properties will not be used in the development, but motivate the 
chosen axioms for DDTOR by showing that the terms satisfy them for their natural destructor:  *)
definition ddtor :: "'a::vvar_TT TT \<Rightarrow> ('a, 'a, 'a TT, 'a TT) F set" where 
  "ddtor t \<equiv> {x . t = cctor x}"

lemma ddtor_ne:  
  "ddtor t \<noteq> {}"  
  unfolding ddtor_def by (auto simp add: TT_nchotomy) 

lemma ddtor_map_TT:
  assumes "{x,x'} \<subseteq> ddtor t"
  shows "\<exists>u. bij (u::'a\<Rightarrow>'a) \<and> |supp u| <o bound(any::'a::vvar_TT) \<and> id_on (FFVarsB x) u \<and> map_F id u id (map_TT u) x = x'"
  using assms TT_inject0 by (auto simp: ddtor_def) 

lemma FFVars_ddtor: 
  assumes "x \<in> ddtor t"
  shows "FFVars t = set1_F x \<union> UNION (set3_F x) FFVars \<union> FFVarsB x"
  using assms by (auto simp: ddtor_def FFVars_simps)
(****)

datatype 'a D = D "'a TT" "'a ssfun"

definition DDTOR :: "('a::vvar_TT D \<Rightarrow> ('a, 'a, 'a TT + 'a D , 'a TT + 'a D) F set)" where
  "DDTOR = (\<lambda>d. case d of D t f \<Rightarrow> {map_F (Rep_ssfun f) id (\<lambda>x. Inr (D x f)) (\<lambda>x. Inr (D x f)) x | x.
        t = cctor x \<and> set2_F x \<inter> imsupp (Rep_ssfun f) = {}})"
definition mmapD :: "('a::vvar_TT \<Rightarrow> 'a) \<Rightarrow> 'a D \<Rightarrow> 'a D" where
  "mmapD = (\<lambda>u d. case d of D x f \<Rightarrow> D (map_TT u x) (compSS u f))"
definition FFVarsD :: "'a::vvar_TT D \<Rightarrow> 'a set" where
  "FFVarsD = (\<lambda>d. case d of D x f \<Rightarrow> FFVars x \<union> imsupp (Rep_ssfun f))"

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
            intro!: exI[of _ "u"] F_map_cong)
         apply (auto simp: imsupp_def supp_def) []
        subgoal premises prems
          supply prems(6,7)[transfer_rule] supp_inv_bound[transfer_rule] bij_imp_bij_inv[transfer_rule]
          using prems(4,5,8,9)
          apply (transfer fixing: u)
          apply (auto simp: prems(6,7) fun_eq_iff)
          subgoal for x p a
            apply (auto simp: imsupp_commute[THEN fun_cong, simplified, of p u "inv u a", symmetric] prems(6))
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
  fixes f :: "'a :: vvar_TT \<Rightarrow> 'a"
  assumes f: "|supp f| <o bound (any :: 'a)"
begin

lift_definition fSS :: "'a ssfun" is f by (rule f)

definition vvsubst where "vvsubst x = ff0 (D x fSS)"

lemma vvsubst_cctor: "set2_F x \<inter> imsupp f = {} \<Longrightarrow>
  vvsubst (cctor x) = cctor (map_F f id vvsubst vvsubst x)"
  unfolding vvsubst_def
  by (subst ff0_DDTOR[unfolded comodel_defs])
    (auto simp: F_map_comp[symmetric] f supp_id_bound o_def id_def[symmetric] Rep_ssfun fSS.rep_eq)

lemma FFVars_vvsubst_weak: "FFVars (vvsubst t) \<subseteq> FFVars t \<union> imsupp f"
  unfolding vvsubst_def
  by (rule order_trans[OF ff0_FFVarsD[unfolded comodel_defs]])
    (auto simp: F_map_comp[symmetric] f supp_id_bound o_def id_def[symmetric] Rep_ssfun fSS.rep_eq)

end

thm vvsubst_cctor FFVars_vvsubst_weak

lemma map_TT_vvsubst:
  fixes f u :: "'a :: vvar_TT \<Rightarrow> 'a"
  assumes f: "|supp f| <o bound (any :: 'a)" and u: "bij u" "|supp u| <o bound (any :: 'a)"
  shows "map_TT u (vvsubst f t) = vvsubst (u o f o inv u) (map_TT u t)"
  unfolding vvsubst_def[OF f] ff0_mmapD[unfolded comodel_defs, OF u, symmetric]
  by (auto simp: vvsubst_def assms ff0_mmapD[unfolded comodel_defs, symmetric] supp_comp_bound supp_inv_bound
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