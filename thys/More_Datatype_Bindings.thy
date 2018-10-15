theory More_Datatype_Bindings 
  imports Datatype_Bindings
begin

lemmas F_set_map_id = F_set_map[OF supp_id_bound bij_id supp_id_bound]

(* *)
lemma wf_subshape: "wf {(t,t') . subshape t t'}"
  unfolding wf_def apply safe
  using subshape_induct by auto

lemma set3_F_subshape: 
  "t \<in> set3_F x \<Longrightarrow> subshape t (ctor x)"
  by (metis T_map_id Un_iff alpha_refl bij_id subshape.intros supp_id_bound)

lemma set4_F_subshape: 
  "t \<in> set4_F x \<Longrightarrow> subshape t (ctor x)"
  by (metis T_map_id Un_iff alpha_refl bij_id subshape.intros supp_id_bound)


(*    *)

lemma F_rel_refl_strong:
  fixes u v :: "'a::var_TT \<Rightarrow> 'a"
  assumes u: "|supp u| <o bound(any::'a)" and v: "bij v" "|supp v| <o bound(any::'a)" 
  assumes "\<And>z1. z1 \<in> set1_F x \<Longrightarrow> u z1 = z1" "\<And>z2. z2 \<in> set2_F x \<Longrightarrow> v z2 = z2"
    "\<And>z3. z3 \<in> set3_F x \<Longrightarrow> P z3 z3" "\<And>z4. z4 \<in> set4_F x \<Longrightarrow> Q z4 z4"
  shows "rel_F u v P Q x x"
proof-
  have 0: "rel_F id id P Q x x" apply(rule F.rel_refl_strong) using assms by auto
  show ?thesis apply(rule F_rel_mono_strong0[OF supp_id_bound u bij_id supp_id_bound v 0])
    using assms by auto
qed

(*  *)

abbreviation "FFVarsB x \<equiv> (UNION (set4_F x) FFVars) - set2_F x"

(*  *)

declare abs_rep_TT2[simp]

(* the absence of classing between the binding variables and the top-free variables: *)
definition noclash :: "('a::var_TT,'a,'a T, 'a T) F \<Rightarrow> bool" where 
  "noclash x \<equiv> set2_F x \<inter> (set1_F x \<union> UNION (set3_F x) FVars) = {}"

lemma noclash_FVars_ctor: 
  "noclash x \<longleftrightarrow> FVars (ctor x) = set1_F x \<union> UNION (set3_F x \<union> set4_F x) FVars - set2_F x"
  unfolding noclash_def by (auto simp: FVars_ctor)

lemma noclash_FVars_ctor_int: 
  "noclash x \<longleftrightarrow> FVars (ctor x) \<inter> set2_F x = {}"
  unfolding noclash_def by (auto simp: FVars_ctor)

lemma noclash_map_F[simp]:
  fixes u :: "'a::var_TT \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o bound(any::'a)"  
  shows "noclash (map_F u u (map_T u) (map_T u) x) \<longleftrightarrow> noclash x" 
  unfolding noclash_def by (auto simp add: u F_set_map FVars_map_T)  

definition nnoclash :: "('a::var_TT,'a,'a TT, 'a TT) F \<Rightarrow> bool" where 
  "nnoclash x \<equiv> set2_F x \<inter> (set1_F x \<union> UNION (set3_F x) FFVars) = {}"

lemma nnoclash_FFVars_cctor: 
  "nnoclash x \<longleftrightarrow> FFVars (cctor x) = set1_F x \<union> UNION (set3_F x \<union> set4_F x) FFVars - set2_F x"
  unfolding nnoclash_def by (auto simp: FFVars_simps)

lemma nnoclash_FFVars_cctor_int:   
  "nnoclash x \<longleftrightarrow> FFVars (cctor x) \<inter> set2_F x = {}"
  unfolding nnoclash_def by (auto simp: FFVars_simps)

lemma map_TT_comp:
  fixes u v :: "'a::var_TT \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o bound(any::'a)" and v: "bij v" "|supp v| <o bound(any::'a)" 
  shows "map_TT (u o v) x = map_TT u (map_TT v x)"
  by (transfer fixing: u v)
    (auto simp: asSS_def T_map_comp supp_comp_bound alpha_refl assms)

lemma FFVars_map_TT:
  fixes u :: "'a::var_TT \<Rightarrow> 'a"
  assumes u: "bij u" "|supp u| <o bound(any::'a)"
  shows "FFVars (map_TT u x) = u ` FFVars x"
  by (transfer fixing: u)
    (auto simp: asSS_def FVars_map_T assms)

end