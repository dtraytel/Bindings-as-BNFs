theory More_Codatatype_Bindings 
  imports Codatatype_Bindings
begin

lemmas F_set_map_id = F_set_map[OF supp_id_bound bij_id supp_id_bound]

(*  *)

abbreviation "FFVarsB x \<equiv> (UNION (set4_F x) FFVars) - set2_F x"

(*   *) 
lemma alpha_cong:
  fixes u v :: "'a::vvar_TT \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o bound(any::'a)" and v: "bij v" "|supp v| <o bound(any::'a)" 
  assumes uv: "\<And> a. a \<in> FVars t \<Longrightarrow> u a = v a"
  shows "alpha (map_T u t) (map_T v t)" 
  by (simp add: alpha_bij alpha_refl u(1) u(2) uv v(1) v(2))

(*  *)

lemma abs_rep_TT: "abs_TT \<circ> rep_TT = id" 
  apply(rule ext)  
  by simp (meson Quotient3_TT Quotient3_def)

lemma abs_rep_TT2[simp]: "abs_TT (rep_TT t) = t"  
  by (simp add: abs_rep_TT comp_eq_dest_lhs)

lemma alpha_rep_abs_TT: "alpha (rep_TT (abs_TT t)) t" 
  using TT.abs_eq_iff abs_rep_TT2 by blast

(*  *)

(* the absence of classing between the binding variables and the top-free variables: *)
definition noclash :: "('a::vvar_TT,'a,'a T, 'a T) F \<Rightarrow> bool" where 
  "noclash x \<equiv> set2_F x \<inter> (set1_F x \<union> UNION (set3_F x) FVars) = {}"

lemma noclash_FVars_ctor: 
  "noclash x \<longleftrightarrow> FVars (ctor x) = set1_F x \<union> UNION (set3_F x \<union> set4_F x) FVars - set2_F x"
  unfolding noclash_def by (auto simp: FVars_ctor)

lemma noclash_FVars_ctor_int: 
  "noclash x \<longleftrightarrow> FVars (ctor x) \<inter> set2_F x = {}"
  unfolding noclash_def by (auto simp: FVars_ctor)

lemma noclash_map_F[simp]:
  fixes u :: "'a::vvar_TT \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o bound(any::'a)"  
  shows "noclash (map_F u u (map_T u) (map_T u) x) \<longleftrightarrow> noclash x" 
  unfolding noclash_def by (auto simp add: u F_set_map FVars_map_T)  

definition nnoclash :: "('a::vvar_TT,'a,'a TT, 'a TT) F \<Rightarrow> bool" where 
  "nnoclash x \<equiv> set2_F x \<inter> (set1_F x \<union> UNION (set3_F x) FFVars) = {}"

lemma nnoclash_FFVars_cctor: 
  "nnoclash x \<longleftrightarrow> FFVars (cctor x) = set1_F x \<union> UNION (set3_F x \<union> set4_F x) FFVars - set2_F x"
  unfolding nnoclash_def by (auto simp: FFVars_simps)

lemma nnoclash_FFVars_cctor_int:   
  "nnoclash x \<longleftrightarrow> FFVars (cctor x) \<inter> set2_F x = {}"
  unfolding nnoclash_def by (auto simp: FFVars_simps)

lemma abs_TT_alpha_aux: 
  assumes u: "bij (u::'a::vvar_TT\<Rightarrow>'a)" "|supp u| <o bound(any::'a)"
    and a: "abs_TT t = abs_TT (map_T u (rep_TT (abs_TT tt)))"
  shows "alpha (map_T u tt) t"  
proof-
  have "alpha t (map_T u (rep_TT (abs_TT tt)))" using a
    using TT.abs_eq_iff by blast
  moreover have "alpha (map_T u (rep_TT (abs_TT tt))) (map_T u tt)"
    unfolding alpha_bij_eq[OF u]  by (simp add: alpha_rep_abs_TT)
  ultimately show ?thesis using alpha_trans alpha_sym by blast
qed

lemma TT_map_comp: 
  fixes u v::"('a::vvar_TT)\<Rightarrow>'a"
  shows 
    "bij u \<Longrightarrow> |supp u| <o bound(any::'a) \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o bound(any::'a) \<Longrightarrow> 
 map_TT (v \<circ> u) t = map_TT v (map_TT u t)"
  by transfer (auto simp add: T_map_comp asSS_def supp_comp_bound alpha_refl)  

lemma TT_map_o: 
  fixes u v::"('a::vvar_TT)\<Rightarrow>'a"
  shows 
    "bij u \<Longrightarrow> |supp u| <o bound(any::'a) \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o bound(any::'a) \<Longrightarrow> 
 map_TT (v \<circ> u) = map_TT v o map_TT u"
  using TT_map_comp unfolding fun_eq_iff by auto

lemma F_rel_comp_imp: 
  fixes x y z :: "('a::vvar_TT, 'a::vvar_TT, 'c, 'd) F"
  assumes 0: "|supp (u::'a\<Rightarrow>'a)| <o bound(any::'a)" "|supp (u'::'a\<Rightarrow>'a)| <o bound(any::'a)"
    "bij (v::'a\<Rightarrow>'a)" "|supp v| <o bound(any::'a)" "bij (v'::'a\<Rightarrow>'a)" "|supp v'| <o bound(any::'a)"
    and 1: "rel_F u v R S x y" "rel_F u' v' R' S' y z"
  shows "rel_F (u' \<circ> u) (v' \<circ> v) (R OO R') (S OO S') x z"
  using F_rel_comp[OF 0, of R R' S S'] 1 unfolding OO_def fun_eq_iff by auto 

lemma alpha_coinduct2[consumes 1, case_names C]: 
  fixes t t' :: "'a::vvar_TT T"
  assumes 0: "\<phi> t t'" and 1:
    "\<And>x x' :: ('a,'a,'a T,'a T)F. \<phi> (ctor x) (ctor x') \<Longrightarrow>
    \<exists>f. |supp f| <o bound(any::'a) \<and> bij f \<and>
    id_on (FVarsB x) f \<and> 
    rel_F id f 
 (\<lambda>t t'. \<phi> t t' \<or> alpha t t')
 (\<lambda>t t'.  \<phi> (map_T f t) t' \<or> alpha (map_T f t) t')
       x x'"
  shows "alpha t t'"
  apply(rule alpha.coinduct[of \<phi>, OF 0])
  using 1 apply auto subgoal for t1 t2 by (cases t1, cases t2) auto .

lemma map_TT_comp:
  fixes u v :: "'a::vvar_TT \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o bound(any::'a)" and v: "bij v" "|supp v| <o bound(any::'a)" 
  shows "map_TT (u o v) x = map_TT u (map_TT v x)"
  by (transfer fixing: u v)
    (auto simp: asSS_def T_map_comp supp_comp_bound alpha_refl assms)

lemma FFVars_map_TT:
  fixes u :: "'a::vvar_TT \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o bound(any::'a)"
  shows "FFVars (map_TT u x) = u ` FFVars x"
  by (transfer fixing: u)
    (auto simp: asSS_def FVars_map_T assms)(* A particular case of vvsubst_cong (for identity) with map_TT instead pf vvsubst *)

lemma map_TT_cong: 
  fixes f g::"'a::vvar_TT \<Rightarrow> 'a" 
  assumes "bij f" "|supp f| <o bound(any::'a)" "bij g" "|supp g| <o bound(any::'a)"
    and "\<And>a. a \<in> FFVars t \<Longrightarrow> f a = g a" 
  shows "map_TT f t = map_TT g t"
  using assms(5)
  apply (coinduction arbitrary: t rule: TT_existential_coinduct)
  subgoal for x y t
    apply (rule fresh_cases[of "supp f \<union> supp g" t])
    apply (simp only: Un_bound assms)
    apply (simp only: imsupp_supp_bound assms map_TT_cctor)
    apply (rule exI conjI refl)+
    apply (simp only: assms F_rel_map supp_id_bound bij_id id_o o_id supp_inv_bound bij_imp_bij_inv)
    apply (rule F_rel_mono_strong0[rotated 6, OF F.rel_eq[THEN predicate2_eqD, THEN iffD2], OF refl])
    apply (auto simp only: supp_id_bound bij_id assms(1-4) o_apply id_apply id_o
      relcompp_apply conversep_iff Grp_def FFVars_simps simp_thms eqTrueI[OF UNIV_I]
      disjoint_eq_subset_Compl subset_eq Compl_iff not_in_supp_alt bij_inv_rev
      bij_comp bij_imp_bij_inv supp_comp_bound supp_inv_bound Un_iff de_Morgan_disj)
    apply force+
    done
  done

end