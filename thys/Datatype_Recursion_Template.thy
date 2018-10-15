theory Datatype_Recursion_Template
  imports More_Datatype_Bindings Template
begin

(* Term-like structures: *)
definition termLikeStr :: "(('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'a set) \<Rightarrow> bool" where 
  "termLikeStr swp fvars \<equiv>
  swp id = id \<and> 
  (\<forall> u v. bij u \<and> |supp u| <o bound (any::'a) \<and> bij v \<and> |supp v| <o bound (any::'a)
      \<longrightarrow> swp (u o v) = swp u o swp v) \<and> 
  (\<forall> u c. bij u \<and> |supp u| <o bound (any::'a) \<and>
      (\<forall> a. a \<in> fvars c \<longrightarrow> u a = a) \<longrightarrow> swp u c = c) \<and>
  (\<forall> u c a. bij u \<and> |supp u| <o bound (any::'a) 
     \<longrightarrow> (u a \<in> fvars (swp u c) \<longleftrightarrow> a \<in> fvars c))"

(* Extended term-like structures (needed for full-fledged recursion): *)
definition termLikeStrC :: "(('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a TT \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a TT \<Rightarrow> 'c \<Rightarrow> 'a set) \<Rightarrow> bool" where 
"termLikeStrC mp fvars \<equiv>
  (\<forall> t. mp id t = id) \<and> 
  (\<forall> u v t. bij u \<and> |supp u| <o bound (any::'a) \<and> bij v \<and> |supp v| <o bound (any::'a)
    \<longrightarrow> mp (u o v) t = mp u t o mp v t) \<and> 
  (\<forall> u c t. bij u \<and> |supp u| <o bound (any::'a) \<and>  
     (\<forall> a. a \<in> fvars t c \<longrightarrow> u a = a) \<longrightarrow> mp u t c = c) \<and>
  (\<forall> u c a t. bij u \<and> |supp u| <o bound (any::'a) \<longrightarrow> 
     (u a \<in> fvars (map_TT u t) (mp u t c) \<longleftrightarrow> a \<in> fvars t c))"

(* Lifting of the map operators to functions involving quotiented terms -- just a useful notation *)
definition mmapfn :: "(('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> 'a TT \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> 
 ('a \<Rightarrow> 'a) \<Rightarrow> 'a TT \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('c \<Rightarrow> 'd)" where 
  "mmapfn swp1 swp2 \<equiv> \<lambda> u t cd c. swp2 u t (cd (swp1 (inv u) c))"

template REC =
(* The model and parameter types: *)
   'a::var_TT C  and 'a::var_TT P
(* Some variables to be avoided (technically subsumed by the parameters, 
   but lighter so we factor them in too) -- see the paper's appendix D.1 *)
fixes A :: "'a::var_TT set"  
  (* Constructor-like operator on the model: *)
and CCTOR :: "('a::var_TT, 'a, 'a TT \<times> ('a P \<Rightarrow> 'a C), 'a TT \<times> ('a P \<Rightarrow> 'a C)) F \<Rightarrow> 'a P \<Rightarrow> 'a C"
  (* Map- and freshness- like operators on the model: *)
and mmapC :: "('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a TT \<Rightarrow> 'a C \<Rightarrow> 'a C"
and FFVarsC :: "'a::var_TT TT \<Rightarrow> 'a C \<Rightarrow> 'a set"
  (* Map- and freshness- like operators for the parameters: *)
and mapP :: "('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a P \<Rightarrow> 'a P"
and FVarsP :: "'a::var_TT P \<Rightarrow> 'a set" 

(* The model axiomatization: *)
assumes  
  small_A: "|A| <o bound (any::'a :: var_TT)"
  and 
  (* The smallness condition that turns a term-like structure into a parameter structure    *)
  small_FVarsP: "\<And> p :: 'a P. |FVarsP p| <o bound (any::'a :: var_TT)"
  and 
  (* Parameters form a term-like structure: *)
  termLikeStr_mapP_FVarsP: "termLikeStr mapP FVarsP" 
  (*  *)
  and   
  (* Next are the two model clauses from the paper, more precisely from the paper's appendix D.2 which 
     deals with full-fledged corecursion). *) 
  (* Condition (VC): *)
  FFVarsC_CCTOR: "\<And> X p. 
  (\<forall> t pd p. (t,pd) \<in> set3_F X \<union> set4_F X \<longrightarrow> FFVarsC t (pd p) \<subseteq> FFVars t \<union> FVarsP p \<union> A)
  \<Longrightarrow> \<comment>\<open> L's twist: \<close> set2_F X \<inter> (FVarsP p \<union> A) = {} 
  \<Longrightarrow> FFVarsC (cctor (map_F id id fst fst X)) (CCTOR X p) \<subseteq> 
      FFVars (cctor (map_F id id fst fst X)) \<union> FVarsP p \<union> A"
  and 
  (* Condition (MC): *)
  mmapC_CCTOR: "\<And> u X (p :: 'a P). 
  bij u \<Longrightarrow> |supp u| <o bound(any::'a :: var_TT) \<Longrightarrow>
  imsupp u \<inter> A = {} \<Longrightarrow>
  mmapC u (cctor (map_F id id fst fst X)) (CCTOR X p) = 
  CCTOR (map_F u u (\<lambda> (t,pd). (map_TT u t, mmapfn mapP mmapC u t pd)) 
                   (\<lambda> (t,pd). (map_TT u t, mmapfn mapP mmapC u t pd)) X) 
        (mapP u p)"
 (* Models form a term-like structure: *)
and termLikeStr_mmapC_FFVarsC: "termLikeStrC mmapC FFVarsC" 

begin

(* Defined analogously to the FVarsB: *)
definition "FFVarsBC X p \<equiv> \<Union> (t,pd) \<in> set4_F X. (FFVars t \<union> FFVarsC t (pd p)) - set2_F X"

abbreviation "mmapPC \<equiv> mmapfn mapP mmapC"

(*  *)
lemma mapP_id[simp,intro!]: "mapP id = id"
  using termLikeStr_mapP_FVarsP unfolding termLikeStr_def by auto

lemma mapP_o: "bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o bound (any::'a) \<Longrightarrow>
  mapP (u o v) = mapP u o mapP v"
  using termLikeStr_mapP_FVarsP unfolding termLikeStr_def by auto

lemma mapP_cong_id: "bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> 
 (\<And> a. a \<in> FVarsP p \<Longrightarrow> u a = a) \<Longrightarrow> mapP u p = p"
  using termLikeStr_mapP_FVarsP unfolding termLikeStr_def by auto

lemma in_FVarsP_mapP[simp]: 
  "bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> 
 u a \<in> FVarsP (mapP u p) \<longleftrightarrow> a \<in> FVarsP p"
  using termLikeStr_mapP_FVarsP unfolding termLikeStr_def by auto

(* *)

lemma mapP_id2[simp,intro!]: "mapP id p = p"
  using mapP_id by simp

lemma mapP_comp: 
  "bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o bound (any::'a) \<Longrightarrow> 
 mapP (u o v) t = mapP u (mapP v t)"
  using termLikeStr_mapP_FVarsP unfolding termLikeStr_def by auto

lemma mapP_bij_inv: 
  assumes "bij (u::'a \<Rightarrow>'a)" "|supp u| <o bound (any::'a::var_TT)"
  shows "bij (mapP u) \<and> inv (mapP u) = mapP (inv u)"
proof-
  have "mapP u o mapP (inv u) = id" by (simp add: assms mapP_o[symmetric] supp_inv_bound)
  moreover have "mapP (inv u) o mapP u = id" by (simp add: assms mapP_o[symmetric] supp_inv_bound)
  ultimately show ?thesis using bij_iff inv_unique_comp by fastforce
qed

lemmas mapP_bij = mapP_bij_inv[THEN conjunct1]
lemmas mapP_inv = mapP_bij_inv[THEN conjunct2]

lemma mapP_cong: 
  assumes b: "bij (u::'a \<Rightarrow>'a)" "|supp u| <o bound (any::'a::var_TT)" and "bij v" "|supp v| <o bound (any::'a)"
    and f: "\<And> a. a \<in> FVarsP p \<Longrightarrow> u a = v a" 
  shows "mapP u p = mapP v p"
proof-
  have "mapP (inv v o u) p = p"
    apply(rule mapP_cong_id) using assms by (auto simp: supp_inv_bound supp_comp_bound)
  thus ?thesis apply (auto simp: assms mapP_comp mapP_inv[symmetric] supp_inv_bound supp_comp_bound )    
    by (metis assms inv_simp2 mapP_bij_inv)
qed

lemma in_FVarsP_mapP_inv: 
  "bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> a \<in> FVarsP (mapP u p) \<longleftrightarrow> inv u a \<in> FVarsP p"
  using in_FVarsP_mapP[of u "inv u a"] by auto

lemma FVarsP_mapP: 
  assumes "bij (u::'a \<Rightarrow>'a)" "|supp u| <o bound (any::'a::var_TT)"
  shows "FVarsP (mapP u p) = {u a | a.  a \<in> FVarsP p}" (is "?L = ?R")
  using assms apply auto subgoal for a apply(rule exI[of _ "inv u a"])
    by (auto simp: in_FVarsP_mapP_inv) .

lemma mapP_inj: 
  "bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> mapP u p = mapP u p' \<longleftrightarrow> p = p'"
  by (simp add: mapP_bij_inv)

(*  *)

(* Version of mmapC_CCTOR that assumes freshness for the parameter as well:   *)
lemma mmapC_CCTOR2:  
  assumes u: "bij (u::'a \<Rightarrow>'a)" "|supp u| <o bound(any::'a::var_TT)"
    and i: "imsupp u \<inter> (FVarsP p \<union> A) = {}"
  shows 
    "mmapC u (cctor (map_F id id fst fst X)) (CCTOR X p) = 
  CCTOR (map_F u u (\<lambda> (t,pd). (map_TT u t,mmapfn mapP mmapC u t pd)) 
                   (\<lambda> (t,pd). (map_TT u t,mmapfn mapP mmapC u t pd)) X) 
        p"
proof-
  have i1: "imsupp u \<inter> FVarsP p = {}" and i2: "imsupp u \<inter> A = {}" using i by auto
  have p: "mapP u p = p" apply(rule mapP_cong_id) using u i1 unfolding imsupp_def supp_def by auto
  show ?thesis using mmapC_CCTOR[OF u i2, of _ p] unfolding p .
qed


(*************************************)
(* The raw-term-based model infrastructure *)

definition CTOR :: "('a::var_TT, 'a, 'a T \<times> ('a P \<Rightarrow> 'a C), 'a T \<times> ('a P \<Rightarrow> 'a C)) F \<Rightarrow> 'a P \<Rightarrow> 'a C" where 
  "CTOR X \<equiv> CCTOR (map_F id id (map_prod abs_TT id) (map_prod abs_TT id) X)"

(* Compatibility of the preterm constructor with alpha: *)
lemma CTOR_alpha: 
  assumes "rel_F id id (rel_prod alpha (=)) (rel_prod alpha (=)) X Y"
  shows "CTOR X = CTOR Y" 
  unfolding CTOR_def apply(rule arg_cong[of _ _ CCTOR])
  unfolding F.rel_eq[symmetric]
    F_rel_map_right_bij[OF supp_id_bound bij_id supp_id_bound bij_id supp_id_bound bij_id supp_id_bound]
    id_o inv_id eq_OO
    F_rel_map_left[OF supp_id_bound supp_id_bound bij_id supp_id_bound bij_id supp_id_bound]
  apply(rule F.rel_mono_strong[OF assms])
  by (auto simp: OO_def Grp_def TT.abs_eq_iff)

(*  *)
lemma mmapC_id[simp,intro!]: "mmapC id t = id"
using termLikeStr_mmapC_FFVarsC unfolding termLikeStrC_def by auto

lemma mmapC_o: 
"bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o bound (any::'a) \<Longrightarrow> 
 mmapC (u o v) t = mmapC u t o mmapC v t"
  using termLikeStr_mmapC_FFVarsC unfolding termLikeStrC_def by auto

lemma mmapC_cong_id: 
"bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> 
 (\<And> a. a \<in> FFVarsC t d \<Longrightarrow> u a = a) \<Longrightarrow> mmapC u t d = d"
  using termLikeStr_mmapC_FFVarsC unfolding termLikeStrC_def by auto

lemma in_FFVarsC_mmapC[simp]: 
"bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> 
 u a \<in> FFVarsC (map_TT u t) (mmapC u t d) \<longleftrightarrow> a \<in> FFVarsC t d"
  using termLikeStr_mmapC_FFVarsC unfolding termLikeStrC_def by auto

(* *)

lemma mmapC_id2[simp,intro!]: "mmapC id t d = d"
using mmapC_id by simp

lemma mmapC_comp: 
"bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o bound (any::'a) \<Longrightarrow> 
 mmapC (u o v) t d = mmapC u t (mmapC v t d)"
  using termLikeStr_mmapC_FFVarsC unfolding termLikeStrC_def by auto

lemma mmapC_bij_inv: 
assumes "bij (u::'a \<Rightarrow>'a)" "|supp u| <o bound (any::'a::var_TT)"
shows "bij (mmapC u t) \<and> inv (mmapC u t) = mmapC (inv u) t"
proof-  
  have "mmapC u t o mmapC (inv u) t = id" by (simp add: assms mmapC_o[symmetric] supp_inv_bound)
  moreover have "mmapC (inv u) t o mmapC u t = id" 
    by (simp add: assms mmapC_o[symmetric] supp_inv_bound)
  ultimately show ?thesis using bij_iff inv_unique_comp by fastforce
qed

lemmas mmapC_bij = mmapC_bij_inv[THEN conjunct1]
lemmas mmapC_inv = mmapC_bij_inv[THEN conjunct2]

lemma mmapC_cong: 
assumes "bij (u::'a \<Rightarrow>'a)" "|supp u| <o bound (any::'a::var_TT)" and "bij v" "|supp v| <o bound (any::'a)" and 
f: "\<And> a. a \<in> FFVarsC t d \<Longrightarrow> u a = v a" 
shows "mmapC u t d = mmapC v t d"  
proof-   
  have "mmapC (inv v o u) t d = d"
    apply(rule mmapC_cong_id) using assms by (auto simp: supp_inv_bound supp_comp_bound)
  thus ?thesis apply (auto simp: assms mmapC_comp mmapC_inv[symmetric] supp_inv_bound supp_comp_bound)  
    by (metis assms inv_simp2 mmapC_bij_inv)
qed

lemma in_FFVarsC_mmapC_inv: 
"bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> 
 a \<in> FFVarsC (map_TT u t) (mmapC u t d) \<longleftrightarrow> inv u a \<in> FFVarsC t d"
  using in_FFVarsC_mmapC[of u "inv u a" t d] by auto

lemma FFVarsC_mmapC: 
assumes "bij (u::'a \<Rightarrow>'a)" "|supp u| <o bound (any::'a::var_TT)"
shows "FFVarsC (map_TT u t) (mmapC u t d) = {u a | a.  a \<in> FFVarsC t d}" (is "?L = ?R")
  using assms apply auto subgoal for a apply(rule exI[of _ "inv u a"])
    by (auto simp: in_FFVarsC_mmapC_inv) .
 
lemma mmapC_inj: 
"bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> 
 mmapC u t d = mmapC u t d' \<longleftrightarrow> d = d'"
  by (simp add: mmapC_bij_inv)

(*  *)
lemma mmapPC_id[simp,intro!]: "mmapPC id t = id"
 unfolding mmapfn_def by auto 
  
lemma mmapPC_o: 
"bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o bound (any::'a) \<Longrightarrow> 
 mmapPC (u o v) t = mmapPC u t o mmapPC v t"
unfolding mmapfn_def 
by (auto simp: fun_eq_iff mapP_comp[symmetric] mapP_inv mmapC_comp 
    supp_inv_bound supp_comp_bound o_inv_distrib)  

(* *)
lemma mmapPC_id2[simp,intro!]: "mmapPC id t d = d"
using mmapPC_id by simp

lemma mmapPC_comp: 
"bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o bound (any::'a) \<Longrightarrow> 
 mmapPC (u o v) t d = mmapPC u t (mmapPC v t d)"
unfolding mmapfn_def 
by (auto simp: fun_eq_iff mapP_comp[symmetric] mapP_inv mmapC_comp 
    supp_inv_bound supp_comp_bound o_inv_distrib)  

lemma mmapPC_bij_inv: 
assumes "bij (u::'a \<Rightarrow>'a)" "|supp u| <o bound (any::'a::var_TT)"
shows "bij (mmapPC u t) \<and> inv (mmapPC u t) = mmapPC (inv u) t"
proof-  
  have "mmapPC u t o mmapPC (inv u) t = id" by (simp add: assms mmapPC_o[symmetric] supp_inv_bound)
  moreover have "mmapPC (inv u) t o mmapPC u t = id" 
    by (simp add: assms mmapPC_o[symmetric] supp_inv_bound)
  ultimately show ?thesis using bij_iff inv_unique_comp by fastforce
qed

lemmas mmapPC_bij = mmapPC_bij_inv[THEN conjunct1]
lemmas mmapPC_inv = mmapPC_bij_inv[THEN conjunct2]

lemma mmapPC_inj: 
"bij (u::'a \<Rightarrow>'a) \<Longrightarrow> |supp u| <o bound (any::'a::var_TT) \<Longrightarrow> 
 mmapPC u t d = mmapPC u t d' \<longleftrightarrow> d = d'"
  by (simp add: mmapPC_bij_inv)

 
(*******)  
(* Any extended model is an "renaming" model: *)
lemma CCTOR_rename:   
  fixes X :: "('a::var_TT, 'a, 'a TT \<times> ('a P \<Rightarrow> 'a C),'a TT \<times> ('a P \<Rightarrow> 'a C)) F" and p u
  defines "x \<equiv> map_F id id fst fst X"  
  defines "X' \<equiv> map_F u u (\<lambda>(t, pd). (map_TT u t, mmapPC u t pd))
                       (\<lambda>(t, pd). (map_TT u t, mmapPC u t pd)) X"
  defines "x' \<equiv> map_F id id fst fst X'"  
  assumes u: "bij u" "|supp u| <o bound(any::'a)"
  and S: "\<forall> t pd p. (t,pd) \<in> set3_F X \<union> set4_F X \<longrightarrow> FFVarsC t (pd p) \<subseteq> FFVars t \<union> FVarsP p \<union> A"
  and u_imsupp: "imsupp u \<inter> (FFVars (cctor x) \<union> FVarsP p \<union> A) = {}" 
  and (* This one does not have to assumed for this proof to go through, 
   meaning the model conditions actually imply a stronger 
   version of CCTOR_rename: *) us: "u ` set2_F X \<inter> set2_F X = {}" 
  shows "CCTOR X p = CCTOR X' p"
proof-
  (*  *)
  from us have *: "set2_F X \<subseteq> imsupp u"
    unfolding imsupp_def supp_def by auto
  have xu: "FFVars (cctor x) \<inter> imsupp u = {}" 
  and u_imsupp': "imsupp u \<inter> (FVarsP p \<union> A) = {}" 
    using u_imsupp by auto
  have iu: "bij (inv u)" "|supp (inv u)| <o bound(any::'a)" 
    using u by (auto simp: supp_inv_bound)
  have Xu: "FFVarsC (cctor x) (CCTOR X p) \<inter> imsupp u = {}" 
    using FFVarsC_CCTOR[OF S, of p] u_imsupp * unfolding x_def by auto
  (*  *)  
  have x_X: "set1_F X = set1_F x"  "set2_F X = set2_F x" 
    "\<And> t pa. (t, pa) \<in> set3_F X \<Longrightarrow> t \<in> set3_F x"
    "\<And> t pa. (t, pa) \<in> set4_F X \<Longrightarrow> t \<in> set4_F x"
    by (force simp: x_def F_set_map supp_id_bound)+
  have 2: "cctor x' = cctor x" unfolding x'_def x_def
  unfolding F_map_comp[symmetric, OF supp_id_bound u(2) bij_id supp_id_bound u] 
  unfolding x_def x'_def X'_def
  apply(rule sym, rule cctor_eq_intro_map_TT[of u])
  apply(auto simp: u F_set_map F_map_comp[symmetric] id_on_def supp_id_bound) 
  subgoal for a t pa  apply(auto dest!: x_X(4) simp: x_X(2))
  using xu[unfolded x_def[symmetric]] unfolding FFVars_simps imsupp_def supp_def by auto 
  subgoal apply(rule F_map_cong)  
  using u supp_id_bound apply auto 
  subgoal for a using xu[unfolded x_def[symmetric]] 
  by (auto simp: FFVars_simps x_X(1) imsupp_def supp_def) 
  subgoal for t pd apply(rule sym, rule map_TT_cong_id[OF u]) 
  using xu[unfolded x_def[symmetric]]    
  by (auto simp: FFVars_simps imsupp_def supp_def dest!: x_X(3)) . .
  have 22: "CCTOR X' p = mmapC u (cctor x) (CCTOR X p)" 
  unfolding mmapC_CCTOR2[OF u u_imsupp', of X, unfolded x_def[symmetric]] 
  apply(rule arg_cong2[of _ _ _ _ CCTOR]) unfolding X'_def by auto     
  have "mmapC (inv u) (cctor x) (CCTOR X p) = CCTOR X p" 
  apply(rule mmapC_cong_id[OF iu]) using Xu[unfolded x_def[symmetric]] 
  unfolding imsupp_inv[OF u(1), symmetric] unfolding imsupp_def supp_def by auto
  also have "\<dots> = mmapC (inv u) (cctor x') (CCTOR X' p)" 
  unfolding 22 F_map_comp[symmetric,OF supp_id_bound supp_id_bound bij_id supp_id_bound u] 
  unfolding 2 unfolding mmapC_comp[OF iu u, symmetric] by (simp add: u)
  finally have "mmapC (inv u) (cctor x) (CCTOR X p) = mmapC (inv u) (cctor x') (CCTOR X' p)" .
  thus ?thesis unfolding 2 x_def[symmetric] unfolding mmapC_inj[OF iu] .
qed

(* Any "renaming" model is a "congruence" model.  *)
lemma CCTOR_cong:
  fixes X X':: "('a::var_TT,'a,'a TT \<times> ('a P \<Rightarrow> 'a C), 'a TT \<times> ('a P \<Rightarrow> 'a C)) F"
  and p::"'a P"
  and u u'::"'a\<Rightarrow>'a" 
  defines "x \<equiv> map_F id id fst fst X" defines "x' \<equiv> map_F id id fst fst X'"
  assumes u: "bij u" "|supp u| <o |UNIV::'a set|" and u': "bij u'" "|supp u'| <o |UNIV::'a set|"
  and S: "\<forall>t pd p. (t, pd) \<in> set3_F X \<union> set4_F X \<longrightarrow> FFVarsC t (pd p) \<subseteq> FFVars t \<union> FVarsP p \<union> A"
  and S': "\<forall>t pd p. (t, pd) \<in> set3_F X' \<union> set4_F X' \<longrightarrow> FFVarsC t (pd p) \<subseteq> FFVars t \<union> FVarsP p \<union> A"
  and imsupp_u: "imsupp u \<inter> (FFVars (cctor x) \<union> FVarsP p \<union> A) = {}" 
  and us: "u ` set2_F X \<inter> set2_F X = {}"
  and imsupp_u': "imsupp u' \<inter> (FFVars (cctor x') \<union> FVarsP p \<union> A) = {}"  
  and us': "u' ` set2_F X' \<inter> set2_F X' = {}"  
  and r: "rel_F (inv u' o u) (inv u' o u)  
        (\<lambda>(t, pd) (t', pd'). map_TT u t = map_TT u' t' \<and> mmapPC u t pd = mmapPC u' t' pd')
        (\<lambda>(t, pd) (t', pd'). map_TT u t = map_TT u' t' \<and> mmapPC u t pd = mmapPC u' t' pd') X X'"
  shows "CCTOR X p = CCTOR X' p" 
proof-
  have iu': "bij (inv u')" "|supp (inv u')| <o |UNIV::'a set|" 
    using u' by(auto simp: supp_inv_bound)
  have "CCTOR X p = CCTOR (map_F u u (\<lambda> (t,pd). (map_TT u t,mmapPC u t pd))
                            (\<lambda> (t,pd). (map_TT u t,mmapPC u t pd)) X) p"
  by(rule CCTOR_rename[OF u S imsupp_u[unfolded x_def] us])   
  also have "\<dots> = CCTOR (map_F u' u' (\<lambda> (t,pd). (map_TT u' t,mmapPC u' t pd))
                        (\<lambda> (t,pd). (map_TT u' t,mmapPC u' t pd)) X') p"
  apply(rule arg_cong2[of _ _ _ _ CCTOR]) apply auto
  unfolding F.rel_eq[symmetric]
    F_rel_map_right_bij[OF supp_id_bound u' bij_id supp_id_bound u']
    o_id inv_id eq_OO
    F_rel_map_left[OF supp_inv_bound[OF u'] u(2) bij_imp_bij_inv[OF u'(1)] supp_inv_bound[OF u'] u]
  apply(rule F_rel_mono_strong1[OF _ _ _ r]) by (auto simp: u iu' supp_comp_bound OO_def Grp_def)  
  also have "\<dots> = CCTOR X' p" by (rule sym, rule CCTOR_rename[OF u' S' imsupp_u'[unfolded x'_def] us'])
  finally show ?thesis .
qed

(* The recursor is developed for these models. *)

definition mapC :: "('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a T \<Rightarrow> 'a C \<Rightarrow> 'a C" where 
  "mapC u t d \<equiv> mmapC u (abs_TT t) d"

definition FVarsC :: "'a::var_TT T \<Rightarrow> 'a C \<Rightarrow> 'a set" where 
  "FVarsC t d \<equiv> FFVarsC (abs_TT t) d"

(* Swapping for functions involving (quotiented) terms -- just a useful notation *)
definition mapfn :: "(('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> 'a T \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> 
 ('a \<Rightarrow> 'a) \<Rightarrow> 'a T \<Rightarrow> ('c \<Rightarrow> 'd) \<Rightarrow> ('c \<Rightarrow> 'd)" where 
  "mapfn swp1 swp2 \<equiv> \<lambda> u t cd c. swp2 u t (cd (swp1 (inv u) c))"

abbreviation "mapPC \<equiv> mapfn mapP mapC" 

lemma mmapPC_abs_TT: "mmapPC u (abs_TT t) pd = mapPC u t pd"
  unfolding fun_eq_iff mapfn_def mmapfn_def by (simp add: mapC_def) 

lemma FVarsC_alpha:
  assumes "alpha t t'"
  shows "FVarsC t' d = FVarsC t d"
  using assms unfolding FVarsC_def  
  using TT.abs_eq_iff by force

lemmas FVars_def2 = FFVars.abs_eq[symmetric]

lemma mapC_alpha:
  assumes "alpha t t'"
  shows "mapC u t = mapC u t'"
  using assms unfolding mapC_def  
  using TT.abs_eq_iff by force 

lemma mapPC_alpha:
  assumes "alpha t t'"
  shows "mapPC u t = mapPC u t'"
  unfolding fun_eq_iff mapfn_def using mapC_alpha[OF assms] by auto

(* The variant of the congruence rule for unquotiented terms: *)
lemma CTOR_cong: 
  assumes 1: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::var_TT)" "bij u'" "|supp u'| <o bound(any::'a)"
    and 2: 
    "\<forall> t pd p. (t,pd) \<in> set3_F X \<union> set4_F X \<longrightarrow> FVarsC t (pd p) \<subseteq> FVars t \<union> FVarsP p \<union> A"
    "\<forall> t pd p. (t,pd) \<in> set3_F X' \<union> set4_F X' \<longrightarrow> FVarsC t (pd p) \<subseteq> FVars t \<union> FVarsP p \<union> A"
    (*  *) 
    "imsupp u \<inter> (FVars (ctor (map_F id id fst fst X)) \<union> FVarsP p \<union> A) = {}" 
    "u ` set2_F X \<inter> set2_F X = {}"
    "imsupp u' \<inter> (FVars (ctor (map_F id id fst fst X')) \<union> FVarsP p \<union> A) = {}"
    "u' ` set2_F X' \<inter> set2_F X' = {}"
    "rel_F (inv u' o u) (inv u' o u)
     (\<lambda>(t,pd) (t',pd'). alpha (map_T u t) (map_T u' t') \<and> mapPC u t pd = mapPC u' t' pd')
     (\<lambda>(t,pd) (t',pd'). alpha (map_T u t) (map_T u' t') \<and> mapPC u t pd = mapPC u' t' pd') 
     X X'"
  shows "CTOR X p = CTOR X' p"  
proof-
  have iu: "bij (inv u' \<circ> u)" "|supp (inv u' \<circ> u)| <o bound(any::'a)" using 1 
    by(auto simp: supp_inv_bound supp_comp_bound)
  have [simp]: "asSS (asBij u) = u" "asSS (asBij u') = u'" using 1 unfolding asSS_def by simp_all 
  show ?thesis
    unfolding CTOR_def apply(rule CCTOR_cong[OF 1]) 
    subgoal using 2(1) unfolding FVarsC_def FVars_def2 F_set_map_id image_def by fastforce 
    subgoal using 2(2) unfolding FVarsC_def FVars_def2 F_set_map_id image_def by fastforce
    subgoal using 2(3) unfolding FVarsC_def FVars_def2 F_set_map_id image_def F.map_comp  
      by (auto simp: F.map_comp abs_TT_ctor)  
    subgoal using 2(4) unfolding FVarsC_def FVars_def2 F_set_map_id image_def F.map_comp  
      by (auto simp: F.map_comp abs_TT_ctor)
    subgoal using 2(5) unfolding FVarsC_def FVars_def2 F_set_map_id image_def F.map_comp  
      by (auto simp: F.map_comp abs_TT_ctor)
    subgoal using 2(6) unfolding FVarsC_def FVars_def2 F_set_map_id image_def F.map_comp  
      by (auto simp: F.map_comp abs_TT_ctor)
    subgoal unfolding F_rel_map_left[OF iu(2) supp_id_bound iu bij_id supp_id_bound] apply simp
      unfolding F_rel_map_right_bij[OF iu(2) bij_id supp_id_bound iu bij_id supp_id_bound] apply simp
      apply(rule F_rel_mono_strong1[OF _ _ _ 2(7)])
          apply(auto simp: iu Grp_def OO_def)
      unfolding map_TT.abs_eq apply (auto simp: TT.abs_eq_iff)
      unfolding mmapfn_def mapfn_def fun_eq_iff mapC_def by auto .
qed    

(* Raw-term-based version of the assumptions: *)
(* For the first block: *) 
lemma FVarsC_CTOR:  
  assumes "\<forall> t pd p. (t,pd) \<in> set3_F X \<union> set4_F X \<longrightarrow> FVarsC t (pd p) \<subseteq> FVars t \<union> FVarsP p \<union> A"
    and "set2_F X \<inter> (FVarsP p \<union> A) = {}"
  shows "FVarsC (ctor (map_F id id fst fst X)) (CTOR X p) \<subseteq> 
       FVars (ctor (map_F id id fst fst X)) \<union> FVarsP p \<union> A"
proof-
  let ?X = "map_F id id (map_prod abs_TT id) (map_prod abs_TT id) X"
  have 0: "map_F id id (abs_TT \<circ> fst) (abs_TT \<circ> fst) X = map_F id id fst fst ?X" 
    unfolding F.map_comp by simp
  show ?thesis
    unfolding CTOR_def 
    unfolding FVarsC_def FVars_def2 F_set_map_id image_def abs_TT_ctor F.map_comp 
    unfolding 0
    apply(rule FFVarsC_CCTOR) using assms by (auto simp: F_set_map_id FVarsC_def FVars_def2)+
qed

(* For the third block: *) 
lemma mapC_CTOR:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::var_TT)" "imsupp u \<inter> A = {}"
  shows "mapC u (ctor (map_F id id fst fst X)) (CTOR X p) = 
  CTOR (map_F u u (\<lambda> (t,pd). (map_T u t, mapfn mapP mapC u t pd)) 
                  (\<lambda> (t,pd). (map_T u t, mapfn mapP mapC u t pd)) X) 
       (mapP u p)"
proof-
  let ?X = "map_F id id (map_prod abs_TT id) (map_prod abs_TT id) X"
  have 0: "map_F id id (abs_TT \<circ> fst) (abs_TT \<circ> fst) X = map_F id id fst fst ?X" 
    unfolding F.map_comp by simp
  have [simp]: "asSS (asBij u) = u" using u unfolding asSS_def asBij_def by simp 
  show ?thesis
    unfolding CTOR_def 
    unfolding mapC_def F_map_comp[symmetric, OF supp_id_bound u(2) bij_id supp_id_bound u(1,2)]    
    apply simp
    unfolding abs_TT_ctor F.map_comp   
    unfolding 0 unfolding mmapC_CCTOR[OF u]
    apply(rule arg_cong2[of _ _ _ _ CCTOR]) 
    unfolding F_map_comp[OF u(2) supp_id_bound u(1,2) bij_id supp_id_bound, symmetric] apply auto
    apply(rule F_map_cong[OF u(2) u(2) u(1,2) u(1,2)]) 
    by (auto simp: map_TT.abs_eq mapfn_def mmapfn_def)  
qed

lemma mapPC_CTOR:
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::var_TT)" "imsupp u \<inter> A = {}"
  shows 
    "mapPC u (ctor (map_F id id fst fst X)) (CTOR X) = 
 CTOR (map_F u u (\<lambda> (t,pd). (map_T u t, mapfn mapP mapC u t pd)) 
                 (\<lambda> (t,pd). (map_T u t, mapfn mapP mapC u t pd)) X)"
proof-
  have iu: "bij (inv u)" "|supp (inv u)| <o bound(any::'a)"
    using u by (auto simp: supp_inv_bound)
  show ?thesis 
    apply(subst mapfn_def) unfolding fun_eq_iff
    unfolding mapC_CTOR[OF assms] mapP_comp[OF u(1,2) iu,symmetric] by (simp add: u)
qed

(*    *) 

definition suitable ::  "(('a::var_TT,'a,'a T,'a T)F \<Rightarrow> 'a P \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> bool" where 
  "suitable pick \<equiv>
 \<forall> x p. bij (pick x p) \<and> |supp (pick x p)| <o bound(any::'a) \<and>  
        imsupp (pick x p) \<inter> (FVars (ctor x) \<union> FVarsP p \<union> A - set2_F x) = {} \<and> 
        pick x p ` (set2_F x) \<inter> (FVars (ctor x) \<union> FVarsP p \<union> A) = {}"

lemma suitable_FVarsB: 
  assumes "suitable pick"
  shows "imsupp (pick x p) \<inter> FVarsB x = {}"
proof- 
  have "FVarsB x \<subseteq> FVars (ctor x) \<union> FVarsP p \<union> A - set2_F x"
    unfolding suitable_def by (auto intro:  FVars_intros(3))
  thus ?thesis using assms unfolding suitable_def by auto
qed

function f :: "(('a::var_TT,'a,'a T,'a T)F \<Rightarrow> 'a P \<Rightarrow> ('a \<Rightarrow> 'a)) \<Rightarrow> 'a T \<Rightarrow> 'a P \<Rightarrow> 'a C" where
  "f pick (ctor x) p =
 (if suitable pick 
 then let x' = map_F id (pick x p) id (map_T (pick x p)) x in 
      CTOR (map_F id id (\<lambda> t. (t, f pick t)) (\<lambda> t. (t, f pick t)) x') p
 else undefined)" 
  by pat_completeness auto
termination   
  apply (relation "inv_image {(s,t). subshape s t} (fst o snd)")
    apply (auto simp: wf_subshape suitable_def F_set_map supp_id_bound)
  subgoal by (auto intro: set3_F_subshape)
  subgoal for pick x p t
    apply(rule subshape.intros[of "inv (pick x p)"]) 
    by ( auto simp: suitable_def supp_inv_bound T_map_comp[symmetric] T_map_id alpha_refl) .

declare f.simps[simp del]

lemma f_simps[simp]:
  assumes "suitable pick"
  shows "f pick (ctor x) p =
 CTOR (map_F id (pick x p) 
         (\<lambda> t. (t, f pick t))
         (\<lambda> t. (map_T (pick x p) t, f pick (map_T (pick x p) t))) 
         x) p"
  using assms apply(simp add: f.simps)
  apply(simp add: suitable_def F_map_comp[symmetric] supp_id_bound)
  apply(rule arg_cong2[of _ _ _ _ CTOR]) apply auto
  apply(rule F_map_cong) by (auto simp: supp_id_bound)

(*  *)

lemma f_FVars: 
  assumes p: "suitable pick"  
  shows "FVarsC t (f pick t p) \<subseteq> FVars t \<union> FVarsP p \<union> A"
proof (induction t arbitrary: p rule: subshape_induct)
  case (subsh t p)
  obtain x where t: "t = ctor x" 
    (* and "set2_F x \<inter> (FVarsP p \<union> A) = {}"
   find_theorems name: avoid *)   
    by (cases t)
  have pick: "bij (pick x p)" "|supp (pick x p)| <o bound(any::'a)" and 
    ipick: "imsupp (pick x p) \<inter> FVarsB x = {}" "pick x p ` set2_F x \<inter> (FVarsP p \<union> A) = {}"
    using p unfolding suitable_def using suitable_FVarsB[OF p] by fastforce+
  have invpick: "bij (inv (pick x p))" "|supp (inv (pick x p))| <o bound(any::'a)"
    using pick by (auto simp: supp_inv_bound)
  let ?X = "(map_F id (pick x p) 
                (\<lambda>t. (t, f pick t))
                (\<lambda>t. (map_T (pick x p) t, f pick (map_T (pick x p) t))) x)"
  define X where "X \<equiv> ?X"
  have al: "alpha (ctor (map_F id id fst fst X)) (ctor x)" 
    using pick unfolding X_def apply(simp add: suitable_def supp_id_bound F_map_comp[symmetric] o_def)
    unfolding id_def[symmetric] apply(rule alpha_sym) apply(rule alpha.intros[OF pick(2,1)])
    subgoal using ipick(1) by (auto simp: id_on_def imsupp_def supp_def FVars_ctor)
    subgoal apply(simp add: F_rel_map supp_id_bound pick Grp_def OO_def) 
      apply(rule F.rel_refl_strong) by (auto simp: alpha_refl) .
  have "FVarsC (ctor (map_F id id fst fst X)) (CTOR X p) \<subseteq> 
        FVars (ctor (map_F id id fst fst X)) \<union> FVarsP p \<union> A" 
    apply(rule FVarsC_CTOR) apply safe 
    subgoal for tt pd pp xx 
      apply (auto simp: pick F_set_map supp_id_bound X_def)
      using subsh[of tt, unfolded t, OF set3_F_subshape] by auto
    subgoal for tt pd pp xx 
      apply (auto simp: pick F_set_map supp_id_bound X_def)
      using subsh[of tt, unfolded t, OF subshape.intros[OF invpick]]
      by (auto simp add: pick invpick T_map_comp[symmetric] T_map_id intro!: alpha_refl) 
    unfolding X_def using ipick by (auto simp: F_set_map supp_id_bound pick) 
  also have "\<dots> = FVars (ctor x) \<union> FVarsP p \<union> A" using alpha_FVars[OF al] by auto 
  finally have "FVarsC (ctor (map_F id id fst fst X)) (CTOR X p) \<subseteq> FVars (ctor x) \<union> FVarsP p \<union> A" .
  thus ?case using p t 
    apply simp unfolding X_def[symmetric] FVarsC_alpha[OF al] . 
qed


(* The "monster lemma": termLikeStr and alpha must be treated in one shot 
(and we also do "pick"-irrelevance at the same time). 
*)
lemma f_swap_alpha: 
  assumes p: "suitable pick" and p': "suitable pick'"
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::var_TT)" "imsupp u \<inter> A = {}"
  assumes a: "alpha t t'"
  shows "f pick (map_T u t) = mapPC u t (f pick t) \<and> 
       f pick t = f pick' t'" 
  using assms proof (induction t arbitrary: pick pick' u t' rule: subshape_induct)
  case (subsh t pick pick' u t')
  note IHsw = subsh(1)[OF _ _ `suitable pick'` _ _ _ alpha_refl, 
      THEN conjunct1] 
  note u = `bij u` `|supp u| <o bound(any::'a)` `imsupp u \<inter> A = {}`
  note p = `suitable pick`
  note ASsw = p u
  note IHal = subsh(1)[OF _ `suitable pick` _ `bij u` `|supp u| <o |UNIV|` `imsupp u \<inter> A = {}`, 
      THEN conjunct2]               
  note ASal = `suitable pick` `suitable pick'` `alpha t t'`
  obtain x where t: "t = ctor x" by (cases t)
  define xx where "xx = map_F u u (map_T u) (map_T u) x" 
    (*   *)
  have iu: "bij (inv u)" "|supp (inv u)| <o bound(any::'a)" "imsupp (inv u) \<inter> A = {}"
    using u by (auto simp: supp_inv_bound imsupp_inv)  
  have uA: "\<And>a. a \<in> A \<Longrightarrow> u a = a"  
    "\<And>a. u a \<in> A \<Longrightarrow> u a = a" using u(3) unfolding supp_def imsupp_def by auto
      (*   *)
  show ?case proof(intro conjI, rule ext)
    fix p 
    define p_iu where "p_iu \<equiv> mapP (inv u) p"
    define x_u where "x_u \<equiv> map_F u u (map_T u) (map_T u) x"
    have sw_pp: "mapP u p_iu = p" unfolding p_iu_def by (simp add: u iu mapP_comp[symmetric])
    define L where "L \<equiv> pick x_u p \<circ> u"
    define R where "R \<equiv> u \<circ> pick x p_iu" 
    define XXl where 
      "XXl \<equiv> map_F u L 
              (\<lambda>t. (map_T u t, f pick (map_T u t))) 
              (\<lambda>t. (map_T L t, f pick (map_T L t))) x"
    define XXr where 
      "XXr \<equiv> map_F u R 
              (\<lambda>t. (map_T u t, mapPC u t (f pick t)))
              (\<lambda>t. (map_T R t, mapPC u (map_T (pick x p_iu) t) 
                                        (f pick (map_T (pick x p_iu) t)))) x"
      (*  *)
    define X where "X = (map_F id (pick x p_iu) 
             (\<lambda>t. (t, f pick t))
             (\<lambda>t. (map_T (pick x p_iu) t, f pick (map_T (pick x p_iu) t))) x)" 
    have XXr_X: "XXr = map_F u u 
                         (\<lambda>(t, pd). (map_T u t, mapPC u t pd)) 
                         (\<lambda>(t, pd). (map_T u t, mapPC u t pd)) X"
      unfolding XXr_def X_def R_def using p 
      by (simp add: suitable_def u F_map_comp[symmetric] T_map_comp[symmetric] supp_comp_bound supp_id_bound o_def)  
        (*  *)
    have 00: "\<And> t'. t' \<in> set3_F x \<Longrightarrow> f pick (map_T u t') = mapPC u t' (f pick t')"
      using IHsw[OF _ p u, unfolded t, OF set3_F_subshape] . 
    have 11: "\<And> t'. t' \<in> set4_F x \<Longrightarrow> 
        let tt' = (map_T (pick x p_iu) t') in 
        f pick (map_T u tt') = mapPC u tt' (f pick tt')"
      unfolding Let_def apply(rule IHsw[OF _ p u]) unfolding t 
      apply(rule subshape.intros[of "inv (pick x p_iu)"]) 
      using p by (auto simp: suitable_def supp_inv_bound T_map_comp[symmetric] T_map_id alpha_refl)
        (*   *)
    have al: "alpha (ctor x) (ctor (map_F id id fst fst X))"  
    proof(rule alpha.intros[of "pick x p_iu"]) 
      show "|supp (pick x p_iu)| <o |UNIV::'a set|" "bij (pick x p_iu)"
        using p by (auto simp: suitable_def)
      show "id_on (FVarsB x) (pick x p_iu)" using p 
        by (fastforce simp: id_on_def suitable_def imsupp_def supp_def FVars_ctor) 
      show "rel_F id (pick x p_iu) alpha (\<lambda>s. alpha (map_T (pick x p_iu) s)) x (map_F id id fst fst X)"
        using p apply(auto simp: F_rel_map suitable_def X_def Grp_def OO_def supp_id_bound)
        apply(rule F.rel_refl_strong) by (auto simp: alpha_refl)
    qed
      (*  *)
    {fix a assume "a \<in> set2_F x"
      hence "u a \<in> set2_F x_u" unfolding x_u_def by (simp add: u F_set_map)
      hence "L a \<notin> FVars (ctor x_u) \<union> FVarsP p \<union> A" unfolding L_def o_def 
        using p unfolding suitable_def by fastforce
      hence "L a \<notin> u ` FVars (ctor x) \<union> FVarsP p \<union> A" unfolding x_u_def  
        by(auto simp add: u F_set_map FVars_ctor FVars_map_T)    
    } note L1 = this
    {fix a assume "a \<in> FVars (ctor x) \<union> inv u ` FVarsP p \<union> A - set2_F x"
      hence "u a \<in> FVars (ctor x_u) \<union> FVarsP p \<union> A - set2_F x_u" 
        unfolding x_u_def  
        apply(auto simp add: u F_set_map FVars_ctor FVars_map_T) by(simp add:  uA)       
      hence "L a = u a" using p unfolding suitable_def L_def imsupp_def supp_def by auto
    } note L2 = this
      (*  *)
    {fix a assume "a \<in> set2_F x"
      hence "pick x p_iu a \<notin> FVars (ctor x) \<union> FVarsP p_iu \<union> A" 
        using p unfolding suitable_def by fastforce
      hence "R a \<notin> u ` FVars (ctor x) \<union> FVarsP p \<union> A"  
        unfolding R_def p_iu_def FVarsP_mapP[OF iu(1,2)]  
        apply (auto simp add: u(1)) using uA(2) by fastforce  
    } note R1 = this
    {fix a assume "a \<in> FVars (ctor x) \<union> inv u ` FVarsP p \<union> A - set2_F x"
      hence "a \<in> FVars (ctor x) \<union> FVarsP p_iu \<union> A - set2_F x" 
        unfolding p_iu_def FVarsP_mapP[OF iu(1,2)] by auto
      hence "pick x p_iu a = a" using p unfolding suitable_def imsupp_def supp_def by fastforce     
      hence "R a = u a" unfolding R_def by simp
    } note R2 = this
      (*  *)
    have L: "bij L" "|supp L| <o bound(any::'a)" 
      and R: "bij R" "|supp R| <o bound(any::'a)" 
      using u p unfolding L_def R_def by (auto simp: suitable_def supp_comp_bound)  
        (*  *)
    have set1_F_XXl: "set1_F XXl = u ` set1_F x" unfolding XXl_def by (simp add: L u F_set_map)
    have set2_F_XXl: "set2_F XXl = L ` set2_F x" unfolding XXl_def by (simp add: L u F_set_map)    
    have "(\<Union>x\<in>set4_F x. L ` FVars x) - L ` set2_F x = u ` FVarsB x" 
      using L2 apply(auto simp: FVars_ctor) using L 
      apply blast  apply (metis image_iff) using L(1) by fastforce    
    hence FVars_XXl: "FVars (ctor (map_F id id fst fst XXl)) = u ` FVars (ctor x)"
      unfolding XXl_def FVars_ctor by (auto simp add: u L F_map_comp[symmetric] F_set_map FVars_map_T supp_id_bound) 
    have set2_F_XXl_int: "set2_F XXl \<inter> (FVars (ctor (map_F id id fst fst XXl)) \<union> FVarsP p \<union> A) = {}"
      using L1 set2_F_XXl unfolding FVars_XXl by auto
        (*  *)
    have set1_F_XXr: "set1_F XXr = u ` set1_F x" unfolding XXr_def by (simp add: R u F_set_map)
    have set2_F_XXr: "set2_F XXr = R ` set2_F x" unfolding XXr_def by (simp add: R u F_set_map)
    have "(\<Union>x\<in>set4_F x. R ` FVars x) - R ` set2_F x = u ` FVarsB x" 
      using R2 apply(auto simp: FVars_ctor) 
      apply blast  apply (metis image_iff) using R(1) by fastforce
    hence FVars_XXr: "FVars (ctor (map_F id id fst fst XXr)) = u ` FVars (ctor x)"
      unfolding XXr_def FVars_ctor by (auto simp add: u R F_map_comp[symmetric] F_set_map FVars_map_T supp_id_bound)
    have set2_F_XXr_int: "set2_F XXr \<inter> (FVars (ctor (map_F id id fst fst XXr)) \<union> FVarsP p \<union> A) = {}"
      using R1 set2_F_XXr unfolding FVars_XXr by auto
        (*   *)
    have card: "|set2_F XXl| =o |set2_F x|" "|set2_F XXr| =o |set2_F x|"
      unfolding set2_F_XXl set2_F_XXr using bij_card_of_ordIso L(1) R(1) by auto   
    hence card_bound: "|set2_F XXl| <o bound(any::'a)" "|set2_F XXr| <o bound(any::'a)"
      using set2_F_bound by blast+
        (*   *) 
    let ?Sl = "FVars (ctor (map_F id id fst fst XXl)) \<union> FVarsP p \<union> A"
    let ?Sr = "FVars (ctor (map_F id id fst fst XXr)) \<union> FVarsP p \<union> A"
    define S where "S \<equiv> set2_F XXl \<union> ?Sl \<union> set2_F XXr \<union> ?Sr" 
    have "|S| <o bound (any::'a)" unfolding S_def 
      apply(intro regularCard_Un[OF bound_Card_order bound_cinfinite bound_regularCard])
      by (auto simp add: card_bound(1,2) card_of_FVars_bound small_FVarsP small_A)  
    hence "|- S| =o bound (any::'a)" using infinite_UNIV_card_of_minus[of S] 
      by (simp add: `|S| <o bound (any::'a)` Compl_eq_Diff_UNIV var_TT_infinite)
    hence "|set2_F XXl| <o |- S|" using card_bound(1) ordIso_symmetric ordLess_ordIso_trans by blast
    from ordLess_imp_ordLeq[OF this] 
    obtain KK where KKS: "KK \<subseteq> - S" and KKo: "|set2_F XXl| =o |KK|"      
      by (meson internalize_card_of_ordLeq2)     
    have interl: "set2_F XXl \<inter> KK = {}" "set2_F XXl \<inter> ?Sl = {}" "KK \<inter> ?Sl = {}"
      using KKS set2_F_XXl_int unfolding S_def by auto
    obtain v where v: "bij v" "|supp v| <o bound(any::'a)" 
      "imsupp v \<inter> ?Sl = {}" "bij_betw v (set2_F XXl) KK"  
      using ordIso_ex_bij_betw_supp[OF var_TT_infinite set2_F_bound KKo interl] by auto
        (*   *)
    let ?ww = "v o L o (inv R)"
    have ww: "bij_betw ?ww (set2_F XXr) KK"
      apply(rule bij_betw_trans[of _ _ "set2_F x"])
      subgoal unfolding bij_betw_def inj_on_def apply (auto simp: R)  
        using R(1) set2_F_XXr apply auto[1] 
        using R(1) bijection.intro bijection.surj_inv image_f_inv_f set2_F_XXr by fastforce
      subgoal apply(rule bij_betw_trans[of _ _ "set2_F XXl"])
        subgoal unfolding bij_betw_def inj_on_def by (auto simp: v L set2_F_XXl)  
        by (simp add: v(4)) .      
    have interr: "set2_F XXr \<inter> KK = {}" "set2_F XXr \<inter> ?Sr = {}" "KK \<inter> ?Sr = {}"
      using KKS set2_F_XXr_int unfolding S_def by auto
    obtain w where w: "bij w" "|supp w| <o bound(any::'a)" 
      "imsupp w \<inter> ?Sr = {}" "bij_betw w (set2_F XXr) KK" and ew: "eq_on (set2_F XXr) w ?ww"  
      using ex_bij_betw_supp[OF var_TT_infinite set2_F_bound ww interr] by auto
    have evw: "eq_on (set2_F x) (v o L) (w o R)" using ew unfolding eq_on_def
      by (simp add: L R v w set2_F_XXr) 
    {fix a assume "a \<in> FVars (ctor x)" 
      hence "u a \<in> FVars (ctor (map_F id id fst fst XXl))" using FVars_XXl by auto
      hence vua: "v (u a) = u a" using v(3) unfolding imsupp_def supp_def by auto
    } note FVars_vu = this
    {fix a assume "a \<in> FVars (ctor x)" 
      hence "u a \<in> FVars (ctor (map_F id id fst fst XXr))" using FVars_XXr by auto
      hence vua: "w (u a) = u a" using w(3) unfolding imsupp_def supp_def by auto
    } note FVars_wu = this
    note vu =  bij_comp[OF u(1) v(1)] supp_comp_bound[OF v(2) u(2)]
    note ivu = bij_imp_bij_inv[OF vu(1)] supp_inv_bound[OF vu]
    have imv: "imsupp v \<inter> A = {}" and imw: "imsupp w \<inter> A = {}" using v w by auto
        (*  *)
        (*  *)
    have C: "CTOR XXl p = CTOR XXr p" 
    proof(rule CTOR_cong[OF v(1,2) w(1,2)]) 
      show "\<forall>t pd p. (t, pd) \<in> set3_F XXl \<union> set4_F XXl \<longrightarrow> 
                     FVarsC t (pd p) \<subseteq> FVars t \<union> FVarsP p \<union> A"
        unfolding XXl_def using p 
        apply(auto simp: suitable_def u L supp_id_bound F_set_map xx_def FVars_ctor)  
        using f_FVars[OF `suitable pick`] using f_FVars[OF `suitable pick'`]
        by (fastforce simp: imsupp_def supp_def)+ 
    next
      show "\<forall>t pd p. (t, pd) \<in> set3_F XXr \<union> set4_F XXr \<longrightarrow> 
                     FVarsC t (pd p) \<subseteq> FVars t \<union> FVarsP p \<union> A"
        unfolding XXr_def using p 
        apply(auto simp: suitable_def u R supp_id_bound F_set_map FVars_ctor supp_comp_bound) 
        subgoal for p t' a 
          using f_FVars[OF `suitable pick`, of "map_T u t'" p] 00[of t'] by auto
        subgoal for p t' a  
          using f_FVars[OF `suitable pick`, of "map_T u (map_T (pick x p_iu) t')" p] 11[of t'] 
          by (auto simp: u Let_def R_def T_map_comp) .
    next   
      show "imsupp v \<inter> ?Sl = {}" using v(3) . 
      show "imsupp w \<inter> ?Sr = {}" using w(3) . 
    next
      show "rel_F (inv w \<circ> v) (inv w \<circ> v)
   (\<lambda>(t, pd) (t', pd'). alpha (map_T v t) (map_T w t') \<and> mapPC v t pd = mapPC w t' pd')
   (\<lambda>(t, pd) (t', pd'). alpha (map_T v t) (map_T w t') \<and> mapPC v t pd = mapPC w t' pd') XXl XXr"
        unfolding XXl_def XXr_def using p 
        apply(simp add: u L R suitable_def F_rel_map v w supp_comp_bound supp_inv_bound
            Grp_def OO_def )
        apply(rule F_rel_refl_strong) 
        apply (auto simp: v w u L R supp_comp_bound supp_inv_bound)[]
        apply (auto simp: v w u L R supp_comp_bound supp_inv_bound)[]
        apply (auto simp: v w u L R supp_comp_bound supp_inv_bound)[] 
      proof-
        fix a assume a: "a \<in> set1_F x" 
        have "u a \<in> set1_F XXl" using a set1_F_XXl by auto
        hence "u a \<in> FVars (ctor (map_F id id fst fst XXl))"   
          unfolding FVars_ctor by (simp add: F_set_map_id)
        hence vua: "v (u a) = u a" using v(3) unfolding imsupp_def supp_def by auto
            (*  *)
        have "u a \<in> set1_F XXr" using a set1_F_XXr by auto
        hence "u a \<in> FVars (ctor (map_F id id fst fst XXr))" 
          unfolding FVars_ctor by (simp add: F_set_map_id)  
        hence wua: "inv w (u a) = u a" using w(3) unfolding imsupp_inv[OF w(1), symmetric]
          unfolding imsupp_def supp_def by auto
        show "(inv u \<circ> (inv w \<circ> v) \<circ> u) a = a" unfolding o_def vua wua by(simp add: u)
      next
        fix a assume a: "a \<in> set2_F x"           
        thus "(inv R \<circ> (inv w \<circ> v) \<circ> L) a = a" using evw unfolding eq_on_def 
          by(simp add: v w R L)  
      next
        fix tt assume tt: "tt \<in> set3_F x"
        show "alpha (map_T v (map_T u tt)) (map_T w (map_T u tt)) \<and>
                mapPC v (map_T u tt) (f pick (map_T u tt)) = 
                mapPC w (map_T u tt) (mapPC u tt (f pick tt))" (is "?A \<and> ?B")
        proof
          show A: ?A apply(rule alpha_bij) apply(auto simp: u v w FVars_map_T alpha_refl)  
            using FVars_intros(2) FVars_vu FVars_wu tt by fastforce  
          have ss: "subshape tt t" unfolding t by (simp add: set3_F_subshape tt)
          have ssu: "subshape (map_T u tt) t" unfolding t 
            apply(rule subshape.intros[OF iu(1,2) alpha_refl]) 
            using tt by (simp add: u iu T_map_id T_map_comp[symmetric])
          have ssvu: "subshape (map_T v (map_T u tt)) t" unfolding t              
            apply(rule subshape.intros[OF ivu alpha_refl]) 
            using tt by (simp add: u v T_map_comp[symmetric] supp_comp_bound supp_inv_bound T_map_id) 
          show ?B unfolding IHsw[OF ssu p v(1,2) imv, symmetric]          
            unfolding IHsw[OF ss p u, symmetric]
            unfolding IHsw[OF ssu p w(1,2) imw, symmetric] 
            using IHal[OF ssvu p A] . 
        qed
      next
        fix tt assume tt: "tt \<in> set4_F x"
        let ?tt' = "map_T (pick x p_iu) tt"
        show "alpha (map_T v (map_T L tt)) (map_T w (map_T R tt)) \<and>
          mapPC v (map_T L tt) (f pick (map_T L tt)) =
          mapPC w (map_T R tt) (mapPC u ?tt' (f pick ?tt'))" (is "?A \<and> ?B")
        proof
          {fix a assume a: "a \<in> FVars tt"
            have "v (L a) = w (R a)" 
            proof(cases "a \<in> set2_F x")
              case True
              thus ?thesis by (metis comp_apply eq_on_def evw)
            next
              case False
              hence "a \<in> FVars (ctor x)" using tt a by (auto simp: FVars_ctor)
              thus ?thesis by (simp add: FVars_vu FVars_wu False L2 R2)
            qed
          } note vLwR = this
          show A: ?A apply(simp add: v w L R T_map_comp[symmetric]) 
            apply(rule alpha_bij) by (auto simp: v w L R supp_comp_bound vLwR alpha_refl)
          have ss: "subshape tt t" unfolding t by (simp add: set4_F_subshape tt)
          have ssu: "subshape (map_T L tt) t" unfolding t 
            apply(rule subshape.intros[of "inv L", OF _ _ alpha_refl]) 
            unfolding t using tt by (auto simp: L supp_inv_bound T_map_id T_map_comp[symmetric])
          have ss': "subshape ?tt' t" unfolding t 
            apply(rule subshape.intros[of "inv (pick x p_iu)", OF _ _ alpha_refl])  
            unfolding t using tt p 
            by (auto simp: suitable_def supp_inv_bound T_map_id T_map_comp[symmetric])
          have ssR: "subshape (map_T R tt) t" unfolding t   
            apply(rule subshape.intros[of "inv R", OF _ _ alpha_refl])  
            unfolding t using tt 
            by (auto simp: R supp_inv_bound supp_comp_bound T_map_id T_map_comp[symmetric])
          have ssvL: "subshape (map_T v (map_T L tt)) t" unfolding t
            apply(simp add: v L T_map_comp[symmetric])
            apply(rule subshape.intros[of "inv (v o L)", OF _ _ alpha_refl])  
            unfolding t using tt 
            by (auto simp: v L supp_inv_bound supp_comp_bound T_map_id T_map_comp[symmetric])
          show ?B 
            unfolding IHsw[OF ssu p v(1,2) imv, symmetric]          
            unfolding IHsw[OF ss' p u, symmetric]
            using p apply(simp add: suitable_def u T_map_comp[symmetric] R_def[symmetric])
            unfolding IHsw[OF ssR p w(1,2) imw, symmetric] 
            using IHal[OF ssvL p A] .
        qed
      qed
    next
      show "v ` set2_F XXl \<inter> set2_F XXl = {}" 
        using bij_betw_imp_surj_on interl(1) v(4) by blast 
    next
      show "w ` set2_F XXr \<inter> set2_F XXr = {}" 
        using bij_betw_imp_surj_on interr(1) w(4) by blast
    qed
      (*  *)
    show "f pick (map_T u t) p = mapPC u t (f pick t) p"
      unfolding t mapfn_def unfolding mapC_alpha[OF al] 
      unfolding f_simps[OF p] unfolding p_iu_def[symmetric] 
      unfolding X_def[symmetric] unfolding mapC_CTOR[OF u] 
      unfolding sw_pp XXr_X[symmetric]
        (*  *)
      unfolding map_T_simps[OF u(1,2)] unfolding f_simps[OF p] 
        (* unfolding x_u_def[symmetric] *)
      using p apply(simp add: u suitable_def supp_comp_bound supp_id_bound F_map_comp[symmetric])
      unfolding x_u_def[symmetric] unfolding L_def[symmetric]
      unfolding o_def 
      using p apply(simp add: u suitable_def supp_comp_bound T_map_comp[symmetric])
      unfolding L_def[symmetric] XXl_def[symmetric] using C .
        (********************* *)
        (********************* *)
  next
    obtain x' where t': "t' = ctor x'" by (cases t')
    note p' = `suitable pick'`
    show "f pick t = f pick' t'" 
    proof(rule ext)
      fix p 
        (*   *)
      define pk pk' where "pk \<equiv> pick x p" and "pk' \<equiv> pick' x' p"
      have pk: "bij pk" "|supp pk| <o bound(any::'a)"
        "imsupp pk \<inter> (FVars (ctor x) \<union> FVarsP p \<union> A - set2_F x) = {}"
        "pk ` set2_F x \<inter> ((* set2_F x \<union>*) FVars (ctor x) \<union> FVarsP p \<union> A) = {}" 
        and pk': "bij pk'" "|supp pk'| <o bound(any::'a)"
        "imsupp pk' \<inter> (FVars (ctor x') \<union> FVarsP p \<union> A - set2_F x') = {}"
        "pk' ` set2_F x' \<inter> ((* set2_F x' \<union>*) FVars (ctor x') \<union> FVarsP p \<union> A) = {}" 
        using p p' unfolding suitable_def pk_def pk'_def by auto
          (*  *)
      let ?X = "map_F id pk (\<lambda>t. (t, f pick t)) 
                (\<lambda>t. (map_T pk t, f pick (map_T pk t))) x"
      let ?X' = "map_F id pk' (\<lambda>t. (t, f pick' t))
           (\<lambda>t. (map_T pk' t, f pick' (map_T pk' t))) x'"
      define X X' where "X \<equiv> ?X" and "X' \<equiv> ?X'"
      define v v' ::"'a \<Rightarrow> 'a" where "v \<equiv> any 0" and "v' \<equiv> any 1"
        (*  *)
      obtain u where u: "bij u " "|supp u| <o bound(any::'a)" "id_on (FVarsB x) u"
        and rxx': "rel_F id u alpha (\<lambda>s. alpha (map_T u s)) x x'" 
        using `alpha t t'` unfolding t t' by cases 
      have u_set2_F: "u ` (set2_F x) = set2_F x'" 
        using F_set2_transfer[OF supp_id_bound u(1,2), unfolded rel_fun_def, rule_format, OF rxx']
        by (auto simp: Grp_def)
      hence bu: "bij_betw u (set2_F x) (set2_F x')"  
        by (metis bij_imp_bij_betw u(1))
          (*  *)
      have FVars_x_x': "FVars (ctor x) = FVars (ctor x')" using `alpha t t'` unfolding t t' 
        by (simp add: alpha_FVars)
      have set1_F_X: "set1_F X = set1_F x" 
        and set2_F_X: "set2_F X = pk ` (set2_F x)"
        unfolding X_def by(simp_all add: pk F_map_comp[symmetric] FVars_ctor o_def 
            id_def[symmetric] image_def F_set_map supp_id_bound)
      have bpk: "bij_betw pk (set2_F x) (set2_F X)"
        using set2_F_X using bij_imp_bij_betw[OF pk(1)] by auto
      have "FVarsB (map_F id id fst fst X) = FVarsB x"  (is "?L = ?R")
      proof-
        {fix b assume "b \<in> ?L"
          then obtain ss where bpk: "b \<notin> pk ` set2_F x"  and ss: "ss \<in> set4_F x" 
            and bm: "b \<in> pk ` FVars ss"
            unfolding X_def by (auto simp: pk F_set_map FVars_map_T supp_id_bound)
          then obtain a where ass: "a \<in> FVars ss" and b: "b = pk a" by auto
          have "a \<notin> set2_F x" using bpk unfolding b by auto
          hence ac: "a \<in> FVars (ctor x) - set2_F x" using ass ss unfolding FVars_ctor by auto
          hence "b = a" unfolding b using pk unfolding imsupp_def supp_def by auto 
          hence "b \<in> ?R" using ac ss ass by auto
        }
        moreover 
        {fix a assume "a \<in> ?R"
          then obtain tt where an: "a \<notin> set2_F x" and at: "a \<in> FVars tt" and t: "tt \<in> set4_F x" by auto
          hence ac: "a \<in> FVars (ctor x) - set2_F x" unfolding FVars_ctor by auto
          hence pka: "pk a = a" using pk unfolding imsupp_def supp_def by auto 
          hence "a \<in> ?L" 
            using pk t at pka apply (auto simp: pk F_set_map X_def FVars_map_T image_def supp_id_bound)  
            apply (metis (no_types, lifting) FVars_map_T image_eqI pk(1) pk(2))
            using an by blast 
        }
        ultimately show ?thesis by blast
      qed
      hence FVars_X: "FVars (ctor (map_F id id fst fst X)) = FVars (ctor x)"
        unfolding X_def FVars_ctor by (simp add: pk F_set_map supp_id_bound)
      have set2_F_X_int: "set2_F X \<inter> (FVars (ctor (map_F id id fst fst X)) \<union> FVarsP p \<union> A) = {}"
        using pk set2_F_X unfolding FVars_X by auto
          (*  *)
      have set1_F_X': "set1_F X' = set1_F x'" 
        and set2_F_X': "set2_F X' = pk' ` (set2_F x')"
        unfolding X'_def by(simp_all add: pk' F_map_comp[symmetric] FVars_ctor o_def 
            id_def[symmetric] image_def F_set_map supp_id_bound)
      have bpk': "bij_betw pk' (set2_F x') (set2_F X')"
        using set2_F_X' using bij_imp_bij_betw[OF pk'(1)] by auto
      have "FVarsB (map_F id id fst fst X') = FVarsB x'"  (is "?L = ?R")
      proof-
        {fix b assume "b \<in> ?L"
          then obtain ss where bpk: "b \<notin> pk' ` set2_F x'"  and ss: "ss \<in> set4_F x'" 
            and bm: "b \<in> pk' ` FVars ss"
            unfolding X'_def by (auto simp: pk' F_set_map FVars_map_T supp_id_bound)
          then obtain a where ass: "a \<in> FVars ss" and b: "b = pk' a" by auto
          have "a \<notin> set2_F x'" using bpk unfolding b by auto
          hence ac: "a \<in> FVars (ctor x') - set2_F x'" using ass ss unfolding FVars_ctor by auto
          hence "b = a" unfolding b using pk' unfolding imsupp_def supp_def by auto 
          hence "b \<in> ?R" using ac ss ass by auto
        }
        moreover 
        {fix a assume "a \<in> ?R"
          then obtain tt where an: "a \<notin> set2_F x'" and at: "a \<in> FVars tt" and t: "tt \<in> set4_F x'" by auto
          hence ac: "a \<in> FVars (ctor x') - set2_F x'" unfolding FVars_ctor by auto
          hence pka: "pk' a = a" using pk' unfolding imsupp_def supp_def by auto 
          hence "a \<in> ?L" 
            using pk' t at pka apply (auto simp: pk' F_set_map X'_def FVars_map_T image_def supp_id_bound)
            apply (metis (no_types, lifting) FVars_map_T image_eqI pk'(1) pk'(2))
            using an by blast 
        }
        ultimately show ?thesis by blast
      qed 
      hence FVars_X': "FVars (ctor (map_F id id fst fst X')) = FVars (ctor x')"
        unfolding X'_def FVars_ctor by (simp add: pk' F_set_map supp_id_bound)
      have set2_F_X'_int: "set2_F X' \<inter> (FVars (ctor (map_F id id fst fst X')) \<union> FVarsP p \<union> A) = {}"
        using pk' set2_F_X' unfolding FVars_X' by auto
          (*  *) 
          (*   *) 
      let ?Ss = "FVars (ctor (map_F id id fst fst X)) \<union> FVarsP p \<union> A"
      let ?Ss' = "FVars (ctor (map_F id id fst fst X')) \<union> FVarsP p \<union> A"
      define S where "S \<equiv> set2_F X \<union> ?Ss \<union> set2_F X' \<union> ?Ss'" 
      have "|S| <o bound (any::'a)" unfolding S_def 
        apply(intro regularCard_Un[OF bound_Card_order bound_cinfinite bound_regularCard])
        by (auto simp add:  card_of_FVars_bound small_FVarsP small_A set2_F_bound) 
      hence "|- S| =o bound (any::'a)" using infinite_UNIV_card_of_minus[of S] 
        by (simp add: `|S| <o bound (any::'a)` Compl_eq_Diff_UNIV var_TT_infinite)
      hence "|set2_F X'| <o |- S|" using ordIso_symmetric ordLess_ordIso_trans  
        using set2_F_bound by blast
      from ordLess_imp_ordLeq[OF this] 
      obtain KK where KKS: "KK \<subseteq> - S" and KKo: "|set2_F X'| =o |KK|"      
        by (meson internalize_card_of_ordLeq2)   
      have inter': "set2_F X' \<inter> KK = {}" "set2_F X' \<inter> ?Ss' = {}" "KK \<inter> ?Ss' = {}"
        using KKS set2_F_X'_int unfolding S_def by auto 
      obtain v' where v': "bij v'" "|supp v'| <o bound(any::'a)" 
        "imsupp v' \<inter> ?Ss' = {}" and pv': "bij_betw v' (set2_F X') KK"  
        using ordIso_ex_bij_betw_supp[OF var_TT_infinite set2_F_bound KKo inter']     
        by auto
      have v'A: "imsupp v' \<inter> A = {}" using v' by auto
          (*   *)
      let ?vv = "v' o pk' o u o (inv pk)"
      have vv: "bij_betw ?vv (set2_F X) KK"
        apply(rule bij_betw_trans[of _ _ "set2_F x"]) 
        using bij_bij_betw_inv[OF pk(1) bpk] apply simp
        apply(rule bij_betw_trans[of _ _ "set2_F x'"])
        using bu apply simp
        apply(rule bij_betw_trans[of _ _ "set2_F X'"])
        using bpk' apply simp 
        using pv' by simp      
      have inter: "set2_F X \<inter> KK = {}" "set2_F X \<inter> ?Ss = {}" "KK \<inter> ?Ss = {}"
        using KKS set2_F_X_int unfolding S_def by auto 
      obtain v where v: "bij v" "|supp v| <o bound(any::'a)" 
        "imsupp v \<inter> ?Ss = {}" "bij_betw v (set2_F X) KK" and ew: "eq_on (set2_F X) v ?vv"  
        using ex_bij_betw_supp[OF var_TT_infinite set2_F_bound vv inter] by auto
      have vA: "imsupp v \<inter> A = {}" using v by auto
      have v4: "v ` set2_F X \<inter> set2_F X = {}"
        using bij_betw_imp_surj_on inter(1) v(4) by blast
      have v'4: "v' ` set2_F X' \<inter> set2_F X' = {}" 
        using bij_betw_imp_surj_on inter'(1) pv' by blast
          (* *)
      have evw: "eq_on (set2_F x) (v' o pk' o u) (v o pk)" using ew unfolding eq_on_def
        by (simp add: v v' u pk set2_F_X)  
          (*  *)
      have C: "CTOR X p = CTOR X' p"  
      proof(rule CTOR_cong[OF v(1,2) v'(1,2) _ _ v(3) v4 v'(3) v'4])
        show "\<forall>t pd p. (t, pd) \<in> set3_F X \<union> set4_F X \<longrightarrow> 
                  FVarsC t (pd p) \<subseteq> FVars t \<union> FVarsP p \<union> A"
          unfolding X_def 
          apply(auto simp add: pk F_set_map image_def supp_id_bound)
          subgoal for t p a 
            using f_FVars[OF `suitable pick`, of t p] by auto
          subgoal for pp a tt 
            using f_FVars[OF `suitable pick`, of "map_T pk tt" pp] by auto .
      next
        show "\<forall>t pd p. (t, pd) \<in> set3_F X' \<union> set4_F X' \<longrightarrow> 
                  FVarsC t (pd p) \<subseteq> FVars t \<union> FVarsP p \<union> A"
          unfolding X'_def 
          apply(auto simp add: pk' F_set_map image_def supp_id_bound)
          subgoal for t p a 
            using f_FVars[OF `suitable pick'`, of t p] by auto
          subgoal for pp a tt 
            using f_FVars[OF `suitable pick'`, of "map_T pk' tt" pp] by auto .
      next
        show "rel_F (inv v' \<circ> v) (inv v' \<circ> v)
     (\<lambda>(t, pd) (t', pd'). alpha (map_T v t) (map_T v' t') \<and> mapPC v t pd = mapPC v' t' pd')
     (\<lambda>(t, pd) (t', pd'). alpha (map_T v t) (map_T v' t') \<and> mapPC v t pd = mapPC v' t' pd') X X'"
          apply(simp add: pk pk' X_def X'_def F_rel_map suitable_def v v' 
              supp_comp_bound supp_inv_bound Grp_def OO_def supp_id_bound) 
          apply(rule F_rel_mono_strong0[OF _ _ _ _ _ _ rxx'])
          apply(auto simp add: pk pk' v v' u supp_comp_bound supp_inv_bound supp_id_bound)
          subgoal for a using v(3) v'(3) unfolding FVars_X FVars_X' imsupp_inv[OF v'(1), symmetric]
            unfolding FVars_x_x'[symmetric]
            unfolding imsupp_def supp_def  unfolding FVars_ctor apply auto  
            by (metis (mono_tags, lifting) Int_iff Un_iff empty_iff mem_Collect_eq) 
          subgoal for a using evw unfolding eq_on_def apply(simp add: v pk v' pk' u) 
            by (metis inv_simp1 pk'(1) v'(1))
        proof-
          fix tt tt'
          assume tt: "tt \<in> set3_F x" and tt': "tt' \<in> set3_F x'" and al: "alpha tt tt'"
          have "alpha (map_T v tt) (map_T v' tt)" apply(rule alpha_bij) 
            using v v' apply auto using tt  
            unfolding FVars_X FVars_X' FVars_x_x'[symmetric] 
            unfolding FVars_ctor imsupp_def supp_def apply (auto simp: alpha_refl)
            by (smt Int_iff UN_I UnCI empty_iff mem_Collect_eq)  
          moreover have "alpha (map_T v' tt) (map_T v' tt')" using alpha_bij_eq v' al by blast
          ultimately show alv: "alpha (map_T v tt) (map_T v' tt')" using alpha_trans by blast
          have ss: "subshape tt t" unfolding t using set3_F_subshape[OF tt] .
          have ss': "subshape tt' t" unfolding t 
            apply(rule subshape.intros[of id _ tt, OF _ _]) using tt alpha_sym[OF al] 
            by (auto simp: T_map_id supp_id_bound)
          have vss: "subshape (map_T v tt) t" unfolding t
            apply(rule subshape.intros[of "inv v" _ tt, OF _ _]) using tt 
            by (auto simp: v supp_inv_bound T_map_comp[symmetric] T_map_id alpha_refl)
          show "mapPC v tt (f pick tt) = mapPC v' tt' (f pick' tt')"
            unfolding IHsw[OF ss p v(1,2) vA, symmetric] IHsw[OF ss' p' v'(1,2) v'A, symmetric]
            using IHal[OF vss p' alv] .
        next 
          fix tt tt'
          assume tt: "tt \<in> set4_F x" and tt': "tt' \<in> set4_F x'"
            and al: "alpha (map_T u tt) tt'" 
          note al' = al[unfolded alpha_bij_eq_inv[OF u(1,2)]]            
          {fix a assume a: "a \<in> FVars tt"
            have "v (pk a) = v' (pk' (u a))" 
            proof(cases "a \<in> set2_F x")
              case True
              thus ?thesis using evw unfolding eq_on_def by auto
            next
              case False
              hence aa: "a \<in> FVarsB x" using a tt unfolding FVars_ctor by auto
              hence a: "a \<in> FVars (ctor x)" using a tt unfolding FVars_ctor by auto
              have pka[simp]: "pk a = a" using pk(3) a False by (auto simp: supp_def imsupp_def)
              have va[simp]: "v a = a" using v(3) a False by (auto simp: FVars_X supp_def imsupp_def)
              have "u a \<in> FVars (ctor x') - set2_F x'"
                using aa a u_set2_F u(3) unfolding id_on_def  apply auto
                using FVars_x_x' a  apply blast
                by (metis bij_implies_inject image_iff u(1))
              hence pk'a[simp]: "pk' (u a) = u a" using pk'(3) by (auto simp: supp_def imsupp_def) 
              have v'a: "v' a = a" using v'(3) a False 
                by (auto simp: FVars_X' FVars_x_x'[symmetric]  supp_def imsupp_def)
              have ua: "u a = a" using u(3) aa unfolding id_on_def by auto
              show ?thesis apply simp  unfolding v'a ua ..                   
            qed
          }  
          hence "alpha (map_T (v \<circ> pk) tt) (map_T (v' \<circ> pk' o u) tt)" 
            apply(intro alpha_bij) by (auto simp: u v v' pk pk' supp_comp_bound alpha_refl)
          moreover have "alpha (map_T (v' \<circ> pk' o u) tt) (map_T (v' \<circ> pk') tt')"
            apply(simp add: T_map_comp v' pk' u supp_comp_bound)
            unfolding alpha_bij_eq[OF v'(1,2)] alpha_bij_eq[OF pk'(1,2)] using al .
          ultimately show alv: "alpha (map_T v (map_T pk tt)) (map_T v' (map_T pk' tt'))" 
            apply(simp add: T_map_comp[symmetric] v v' pk pk')
            using alpha_trans by blast
          have pkss: "subshape (map_T pk tt) t" unfolding t 
            apply(rule subshape.intros[of "inv pk" _ tt]) using tt
            by (auto simp: pk supp_inv_bound T_map_comp[symmetric] T_map_id alpha_refl)
          have pkss': "subshape (map_T pk' tt') t" unfolding t 
            apply(rule subshape.intros[of "inv u o inv pk'" _ tt]) using tt
            by (auto simp: pk' u supp_inv_bound supp_comp_bound T_map_comp[symmetric] 
                o_assoc[symmetric] alpha_sym[OF al'])
          have [simp]: "inv pk \<circ> inv v \<circ> (v \<circ> pk) = id" using o_assoc by (auto simp add: pk v)
          have vpkss: "subshape (map_T v (map_T pk tt)) t" unfolding t 
            apply(simp add: v pk T_map_comp[symmetric])
            apply(rule subshape.intros[of "inv pk o inv v" _ tt]) using tt o_assoc
            by (auto simp: pk v supp_inv_bound supp_comp_bound T_map_comp[symmetric] 
                T_map_id alpha_refl)  
              (*  *)
          show "mapPC v (map_T pk tt) (f pick (map_T pk tt)) = 
                  mapPC v' (map_T pk' tt') (f pick' (map_T pk' tt'))" 
            unfolding IHsw[OF pkss p v(1,2) vA, symmetric] IHsw[OF pkss' p' v'(1,2) v'A, symmetric] 
            using IHal[OF vpkss p' alv] . 
        qed
      qed
        (*  *)
      show "f pick t p = f pick' t' p"
        unfolding t t' using p p' apply simp 
        unfolding pk_def[symmetric] pk'_def[symmetric] X_def[symmetric] X'_def[symmetric] using C .     
    qed    
  qed
qed

lemma f_swap: 
  assumes p: "suitable pick"  
    and u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::var_TT)" "imsupp u \<inter> A = {}"
  shows "f pick (map_T u t) = mapPC u t (f pick t)"
  using f_swap_alpha[OF p p u alpha_refl, THEN conjunct1] .

lemma f_alpha: 
  assumes a: "alpha t t'"
    and p: "suitable pick" and p': "suitable pick'"
  shows "f pick t = f pick' t'" 
proof-
  have u: "bij id" "|supp id| <o bound(any::'a)" "imsupp id \<inter> A = {}" 
    unfolding imsupp_def supp_def by (auto simp: emp_bound)
  show ?thesis
    using f_swap_alpha[OF p p' u a, THEN conjunct2] .
qed


(*******************************)
(* Committing to 'particular pick-fresh function: *)

definition pick0 :: "('a::var_TT, 'a, 'a T, 'a T) F \<Rightarrow> 'a P \<Rightarrow> 'a \<Rightarrow> 'a" where
  "pick0 \<equiv> SOME pick. suitable pick"

lemma exists_suitable: 
  "\<exists> pick. suitable pick" 
proof-
  let ?phi = "\<lambda> x p pk. bij pk \<and>
      |supp pk| <o bound(any::'a::var_TT) \<and>
      imsupp pk \<inter> (FVars (ctor x) \<union> FVarsP p \<union> A - set2_F x) = {} \<and>
      pk ` set2_F x \<inter> (FVars (ctor x) \<union> FVarsP p \<union> A) = {}"
  {fix x::"('a,'a,'a T, 'a T)F" and p ::"'a P"    
    let ?Sr = "FVars (ctor x) \<union> FVarsP p \<union> A - set2_F x"
    define S where "S \<equiv> set2_F x \<union> ?Sr " 
    have SS: "|S| <o bound (any::'a::var_TT)" unfolding S_def apply simp
      apply(intro regularCard_Un[OF bound_Card_order bound_cinfinite bound_regularCard])
      by (auto simp add: card_of_FVars_bound small_FVarsP small_A set2_F_bound)   
    hence "|- S| =o bound (any::'a::var_TT)" using infinite_UNIV_card_of_minus[of S] 
      by (simp add: SS Compl_eq_Diff_UNIV var_TT_infinite)
    hence "|set2_F x| <o |- S|" using set2_F_bound ordIso_symmetric ordLess_ordIso_trans by blast
    from ordLess_imp_ordLeq[OF this] 
    obtain KK where KKS: "KK \<subseteq> - S" and KKo: "|set2_F x| =o |KK|"      
      by (meson internalize_card_of_ordLeq2)     
    have interl: "set2_F x \<inter> KK = {}" "set2_F x \<inter> ?Sr = {}" "KK \<inter> ?Sr = {}"
      using KKS unfolding S_def by auto
    obtain u where u: "bij u" "|supp u| <o bound(any::'a)" 
      "imsupp u \<inter> ?Sr = {}" "bij_betw u (set2_F x) KK"  
      using ordIso_ex_bij_betw_supp[OF var_TT_infinite set2_F_bound KKo interl] by auto
    hence "u ` set2_F x \<subseteq> KK" unfolding bij_betw_def by auto
    hence uu: "u ` set2_F x \<inter> (set2_F x \<union> FVars (ctor x) \<union> FVarsP p \<union> A) = {}" 
      using KKS unfolding S_def by auto
    have "\<exists> u. ?phi x p u" using u uu by blast
  }
  thus ?thesis unfolding suitable_def by metis
qed

lemma suitable_pick0:
  "suitable pick0"
  using someI_ex[OF exists_suitable] unfolding pick0_def[symmetric] .

definition "f0 \<equiv> f pick0"

lemma alpha_f0:
  assumes "alpha t t'"
  shows "f0 t = f0 t'"
  unfolding f0_def apply(rule f_alpha[OF assms]) using suitable_pick0 by auto

lemma f0_low_level_simps: 
  "f0 (ctor x) p =
 CTOR (map_F id (pick0 x p) 
           (\<lambda>t. (t, f0 t)) 
           (\<lambda>t. (map_T (pick0 x p) t, f0 (map_T (pick0 x p) t))) x) p"
  unfolding f0_def f_simps[OF suitable_pick0] ..

lemma f0_ctor: (* Here noclash is needed! *)
  assumes x: "set2_F x \<inter> (FVarsP p \<union> A) = {}" "noclash (x::('a::var_TT, 'a, 'a T, 'a T) F)"
  shows "f0 (ctor x) p = CTOR (map_F id id (\<lambda>t. (t, f0 t)) (\<lambda>t. (t, f0 t)) x) p"
proof- 
  define pick1 where   
    "pick1 \<equiv> \<lambda> x' p'. if (x',p') = (x,p) then id else pick0 x' p'" 
  have 1: "suitable pick1" using suitable_pick0 assms unfolding suitable_def pick1_def apply (auto simp: supp_id_bound)
    unfolding imsupp_def supp_def noclash_FVars_ctor_int by fastforce+  
  have 2: "pick1 x p = id" unfolding pick1_def by simp
  have 3: "f pick1 (ctor x) = f0 (ctor x)" 
    using f_alpha[OF alpha_refl suitable_pick0 1] unfolding f0_def by auto 
  have 4: "f pick1 (ctor x) p = CTOR (map_F id id (\<lambda>t. (t, f0 t)) (\<lambda>t. (t, f0 t)) x) p" 
    unfolding f_simps[OF 1] 2 T_map_id
    apply(rule arg_cong2[of _ _ _ _ CTOR]) apply auto
    apply(rule F_map_cong)
    by (auto simp: 1 suitable_pick0 f0_def intro!: f_alpha alpha_refl supp_id_bound)
  show ?thesis unfolding 3[symmetric] 4 ..  
qed

lemma f0_swap: 
  assumes "bij (u::'a\<Rightarrow>'a)" and "|supp u| <o bound(any::'a::var_TT)" and "imsupp u \<inter> A = {}"
  shows "f0 (map_T u t) x = mapC u t (f0 t (mapP (inv u) x))" 
  using f_swap[OF suitable_pick0, unfolded f0_def[symmetric] mapfn_def fun_eq_iff, OF assms]
  by auto

lemmas f0_FVars = f_FVars[OF suitable_pick0, unfolded f0_def[symmetric]]


(* The following theorems for raw theorems will now be lifted to quotiented terms: *)
thm alpha_f0  
  f0_ctor
  f0_swap f0_FVars
  CTOR_alpha

(*******************)
(* End product: *)
definition ff0 :: "'a::var_TT TT \<Rightarrow> 'a P \<Rightarrow> 'a C" where "ff0 t p = f0 (rep_TT t) p" 

lemma alpha_f0_par:
  assumes "alpha t t'"
  shows "f0 t p = f0 t' p"
  using alpha_f0[OF assms] by simp

lemma nnoclash_noclash: 
  "nnoclash x \<longleftrightarrow> noclash (map_F id id rep_TT rep_TT x)"
  unfolding noclash_def nnoclash_def by (simp add: F_set_map FFVars_def supp_id_bound)  

theorem ff0_cctor:   
  assumes x: "set2_F x \<inter> (FVarsP p \<union> A) = {}" and n: "nnoclash x"
  shows "ff0 (cctor x) p = CCTOR (map_F id id (\<lambda>t. (t, ff0 t)) (\<lambda>t. (t, ff0 t)) x) p"
proof-    
  have 0: "set2_F x = set2_F (map_F id id rep_TT rep_TT x)" by (simp add: F_set_map supp_id_bound)
  show ?thesis unfolding ff0_def cctor_def 
    using f0_ctor[unfolded CTOR_def,symmetric,OF x[unfolded 0]  n[unfolded nnoclash_noclash]]
    apply (simp add: F_map_comp[symmetric] supp_id_bound) unfolding o_def 
    by (auto intro: alpha_f0_par alpha_rep_abs_TT)
qed

theorem ff0_sswap: 
  assumes u: "bij (u::'a\<Rightarrow>'a)" "|supp u| <o bound(any::'a::var_TT)" "imsupp u \<inter> A = {}"
  shows "ff0 (map_TT u t) p = mmapC u t (ff0 t (mapP (inv u) p))"
proof- 
  have [simp]: "asSS u = u" using assms unfolding asSS_def by auto
  show ?thesis unfolding ff0_def using f0_swap[symmetric, OF assms, of "rep_TT t" p]
    apply (auto simp: map_TT_def mapC_def u
        intro: fun_cong[of _ _ p] f_alpha[OF _ suitable_pick0 suitable_pick0, unfolded f0_def[symmetric]]
        alpha_trans[OF alpha_rep_abs_TT]) 
    by (metis alpha_f0 alpha_rep_abs_TT)
qed

theorem ff0_FFVars: 
  "FFVarsC t (ff0 t p) \<subseteq> FFVars t \<union> FVarsP p \<union> A"
  using f0_FVars[of "rep_TT t"] unfolding FFVars_def FVarsC_def ff0_def by simp

end

end