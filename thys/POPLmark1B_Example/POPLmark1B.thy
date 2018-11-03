theory POPLmark1B
imports Custom_POPLmark1B
begin

definition "swap x y z = (if x = z then y else if y = z then x else z)"

lemma swap_itself[simp]: "swap x x = id"
  unfolding swap_def by auto     

lemma bij_swap[simp]: "bij (swap x y)"
  by (rule o_bij[of "swap x y"]) (auto simp: fun_eq_iff swap_def)

lemma supp_swap: "supp (swap x y) = (if x = y then {} else {x, y})"
  unfolding supp_def swap_def by auto

lemma imsupp_swap[simp]: "imsupp (swap x y) = (if x = y then {} else {x, y})"
  unfolding imsupp_def supp_def swap_def by auto

lemma supp_swap_bound[simp]: "|supp (swap x y)| \<le>o bound(any::'a::var_TT)"
  by (auto simp: supp_swap bound_cinfinite bound_Card_order cfinite_def ordLess_imp_ordLeq Cfinite_ordLess_Cinfinite)

lemma finite_supp_swap[simp]: "finite (supp (swap x y))"
  by (auto simp: supp_swap)

lemma swap_eq[simp]:
  "swap x y a = y \<longleftrightarrow> a = x"
  "swap x y a = x \<longleftrightarrow> a = y"
  "y = swap x y a \<longleftrightarrow> a = x"
  "x = swap x y a \<longleftrightarrow> a = y"
  unfolding swap_def by auto

lemma swap_id[simp]: "x \<noteq> a \<Longrightarrow> y \<noteq> a \<Longrightarrow> swap x y a = a"
  unfolding swap_def by simp

lemma swap_swap[simp]: "swap x y o swap y x = id" "swap x y o swap x y = id"
  unfolding swap_def by auto
  
(* For POPLmarkTypes: *)
lemma vvsubst_id2[simp]: "vvsubst id = id" by (auto simp: vvsubst_id)
    
lemma vvsubst_comp: 
  "finite (supp g) \<Longrightarrow> finite (supp f) \<Longrightarrow> 
   vvsubst (g \<circ> f) = vvsubst g o vvsubst f"
  using vvsubst_o[of g f] finite_less_bound[of "supp g"] finite_less_bound[of "supp f"] by force

type_synonym 'a ctxt = "('a \<times> 'a TT) list"
abbreviation "vars_ctxt \<Gamma> \<equiv> fst ` set \<Gamma> \<union> \<Union>(FFVars ` snd ` set \<Gamma>)"

lemma finite_FFVars[simp]: "finite (FFVars (T :: 'a::var_TT TT))"
  by (induct T rule: user_TT_plain_induct) auto

lemmas finite_bound[simp] = bound_cinfinite bound_Card_order cfinite_def
        ordLess_imp_ordLeq Cfinite_ordLess_Cinfinite

definition wf_type :: "'a::{large_G, var_TT} ctxt \<Rightarrow> 'a TT \<Rightarrow> bool" ("_ \<turnstile>\<^sub>w\<^sub>f\<^sub>T _" [51, 51] 50) where
  wf_type_FFVars: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T \<longleftrightarrow> FFVars T \<subseteq> fst ` set \<Gamma>"

inductive wf_ctxt :: "'a::{large_G, var_TT} ctxt \<Rightarrow> bool" ("\<turnstile>\<^sub>w\<^sub>f\<^sub>T _" [51] 50) where
  WF_Nil:  "\<turnstile>\<^sub>w\<^sub>f\<^sub>T []"
| WF_Cons: " \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow> x \<notin> fst ` set \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f\<^sub>T (x, T) # \<Gamma>"

declare wf_ctxt.intros[intro!]

inductive_cases wf_ctxtE:
  "\<turnstile>\<^sub>w\<^sub>f\<^sub>T X # \<Gamma>"

inductive subtyping :: "'a::{large_G, var_TT} ctxt \<Rightarrow> 'a TT \<Rightarrow> 'a TT \<Rightarrow> bool"
  ("_ \<turnstile> _ <: _" [51, 51, 51] 50)
where
  SA_TTop[intro!]:      "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T \<Longrightarrow> \<Gamma> \<turnstile> T <: TTop"
| SA_TVar_Refl[intro!]: "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow> X \<in> fst ` set \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> TVar X <: TVar X"
| SA_TVar_Trans[intro]: "(X, U) \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> U <: T \<Longrightarrow> \<Gamma> \<turnstile> TVar X <: T"
| SA_TArr[intro!]:      "\<Gamma> \<turnstile> T1 <: S1 \<Longrightarrow> \<Gamma> \<turnstile> S2 <: T2 \<Longrightarrow> \<Gamma> \<turnstile> TArr S1 S2 <: TArr T1 T2"
| SA_TAll[intro!]:      "\<Gamma> \<turnstile> T1 <: S1 \<Longrightarrow> x \<notin> fst ` set \<Gamma> \<Longrightarrow> (x, T1) # \<Gamma> \<turnstile> S2 <: T2 \<Longrightarrow> \<Gamma> \<turnstile> TAll x S1 S2 <: TAll x T1 T2"
| SA_TRec[intro!]:      "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T TRec X \<Longrightarrow> labels X \<subseteq> labels Y \<Longrightarrow> (\<And>x T. (x, T) \<in>\<in> Y \<Longrightarrow> \<exists>S. (x, S) \<in>\<in> X \<and> \<Gamma> \<turnstile> S <: T) \<Longrightarrow>
                          \<Gamma> \<turnstile> TRec X <: TRec Y"

inductive_cases
  subtyping_TVarRE[elim]:  "\<Gamma> \<turnstile> S <: TVar X" and
  subtyping_TTopRE[elim]:  "\<Gamma> \<turnstile> S <: TTop" and
  subtyping_TArrRE[elim]:  "\<Gamma> \<turnstile> S <: TArr T U" and
  subtyping_TAllRE[elim]:  "\<Gamma> \<turnstile> S <: TAll x T U" and
  subtyping_TRecRE[elim]:  "\<Gamma> \<turnstile> S <: TRec X" and
  subtyping_TVarLE[elim]:  "\<Gamma> \<turnstile> TVar X <: S" and
  subtyping_TTopLE[elim!]: "\<Gamma> \<turnstile> TTop <: S" and
  subtyping_TArrLE[elim]:  "\<Gamma> \<turnstile> TArr T U <: S" and
  subtyping_TAllLE[elim]:  "\<Gamma> \<turnstile> TAll x T U <: S" and
  subtyping_TRecLE[elim]:  "\<Gamma> \<turnstile> TRec X <: S"
  
  (* Crucial well-scoping property: No loose variables. *)
  
lemma subtyping_wf_ctxt[simp]: "\<Gamma> \<turnstile> T <: U \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma>"
  by (induct \<Gamma> T U rule: subtyping.induct) auto

lemma subtyping_wf_type[simp]: "\<Gamma> \<turnstile> T <: U \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T \<and> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T U"
  by (induct \<Gamma> T U rule: subtyping.induct)
    (force simp: wf_type_FFVars image_iff subset_eq dest!: values_lfin)+
  
(* Invariance under bijective subsitution:   *)
 
lemma vvsubst_wf_type: 
  "bij f \<Longrightarrow> finite (supp f) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T \<Longrightarrow> 
   map (map_prod f (vvsubst f)) \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T vvsubst f T"
  by (auto simp: wf_type_FFVars image_image FFVars_vvsubst)
    
lemma vvsubst_wf_ctxt: "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow> bij f \<Longrightarrow> finite (supp f) \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f\<^sub>T map (map_prod f (vvsubst f)) \<Gamma>"
  by (induct \<Gamma> rule: wf_ctxt.induct) (force simp: vvsubst_wf_type split: if_split)+

lemma subtyping_vvsubst:
  assumes "\<Gamma> \<turnstile> T <: U" and "bij f" and "finite (supp f)"
  shows "map (map_prod f (vvsubst f)) \<Gamma> \<turnstile> vvsubst f T <: vvsubst f U"
  using assms  
  by (induct \<Gamma> T U rule: subtyping.induct)
    (auto 0 3 simp: vvsubst_wf_ctxt lfin_map_lfset wf_type_FFVars FFVars_vvsubst
    o_eq_dest[OF lfset_set1_map] o_eq_dest[OF lfset_set2_map] image_image, force+)
  
(*  ... and in particular under swapping: *)
abbreviation "vvswap x y \<equiv> vvsubst (swap x y)"
abbreviation "swap_ctxt x y \<equiv> map (map_prod (swap x y) (vvswap x y))"
    
lemma FFVars_vvswap[simp]: "FFVars (vvswap x y t) = {swap x y z |z. z \<in> FFVars t}"
  by (rule FFVars_vvsubst) simp
  
lemma swap_same[simp]: "swap x x' x = x'" unfolding swap_def by simp
    
lemma vvswap_idle[simp]: 
assumes "x \<notin> FFVars T" "x' \<notin> FFVars T" shows "vvswap x' x T = T"  
proof-
  have "vvswap x' x T = vvsubst id T" 
  using assms by (intro vvsubst_cong) (auto simp: swap_def supp_id_bound)
  thus ?thesis by auto
qed
  
lemma wf_ctxt_snd_fst: 
  assumes "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma>" 
  shows "\<Union> (FFVars ` snd ` set \<Gamma>) \<subseteq> fst ` set \<Gamma>"
  using assms by induction (auto simp: wf_type_FFVars)

lemma swap_ctxt_idle: 
assumes "x \<notin> fst ` set \<Gamma>" and "x \<notin> \<Union> (FFVars ` snd ` set \<Gamma>)"
   and "x' \<notin> fst ` set \<Gamma>" and "x' \<notin> \<Union> (FFVars ` snd ` set \<Gamma>)"
shows "swap_ctxt x x' \<Gamma> = \<Gamma>"
  using assms by (induction \<Gamma>) (auto simp: swap_def) 
    
lemma swap_wf_ctxt_idle[simp]: 
assumes g: "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma>" and x: "x \<notin> fst ` set \<Gamma>" and x': "x' \<notin> fst ` set \<Gamma>" 
shows "swap_ctxt x x' \<Gamma> = \<Gamma>"
using wf_ctxt_snd_fst[OF g] swap_ctxt_idle[OF x _ x'] x x' by auto

lemma vvswap_wf_type: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T \<Longrightarrow> swap_ctxt x y \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T vvswap x y T"
  using vvsubst_wf_type[OF bij_swap finite_supp_swap] .
 
lemma vvswap_wf_ctxt: "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f\<^sub>T swap_ctxt x y \<Gamma>"
  using vvsubst_wf_ctxt[OF _ bij_swap finite_supp_swap] .

lemma subtyping_vvswap:
"\<Gamma> \<turnstile> T <: U \<Longrightarrow> 
 map (map_prod (swap x y) (vvsubst (swap x y))) \<Gamma> \<turnstile> vvsubst (swap x y) T <: vvsubst (swap x y) U"
  using subtyping_vvsubst[OF _ bij_swap finite_supp_swap] . 
    
(* Fresh induction infrastructure: *)
    
(* First equivariance closure *)
definition cl where "cl \<phi> \<Gamma> T U \<rho> = (\<forall> f. bij f \<and> finite (supp f) \<longrightarrow> 
      \<phi> (map (map_prod f (vvsubst f)) \<Gamma>) (vvsubst f T) (vvsubst f U) \<rho>)"
  
lemmas clI[intro] = iffD2[OF cl_def, rule_format]
  
lemma clE[elim]: 
assumes "cl \<phi> \<Gamma> T U \<rho>" and "bij f" "finite (supp f)"
shows "\<phi> (map (map_prod f (vvsubst f)) \<Gamma>) (vvsubst f T) (vvsubst f U) \<rho>"
  using assms unfolding cl_def by auto
    
lemma clE_vvswap[elim]: 
assumes "cl \<phi> \<Gamma> T U \<rho>" 
shows "\<phi> (map (map_prod (swap x y) (vvsubst (swap x y))) \<Gamma>) (vvswap x y T) (vvswap x y U) \<rho>"
apply(rule clE[OF assms]) using bij_swap finite_supp_swap by auto
  
lemma cl_ext: "cl \<phi> \<Gamma> T U \<rho> \<Longrightarrow> \<phi> \<Gamma> T U \<rho>"
  unfolding cl_def by (auto elim: allE[of _ id] simp: supp_id) 
    
lemma cl_vvsubst:
  assumes f: "bij f" "finite (supp f)" and cl: "cl \<phi> \<Gamma> T U \<rho>"
  shows "cl \<phi> (map (map_prod f (vvsubst f)) \<Gamma>) (vvsubst f T) (vvsubst f U) \<rho>"
  using assms unfolding cl_def apply safe subgoal for g 
 by (auto simp: finite_supp_comp map_prod.comp vvsubst_comp elim!: allE[of _ "g o f"]) . 

lemma cl_cl: "cl (cl \<phi>) = cl \<phi>" 
  by (intro ext) (metis cl_def cl_ext cl_vvsubst)
    
lemma finite_obtains:
assumes "finite (A::'a::{large_G,var_TT} set)"
obtains x where "x \<notin> A"
proof-
  have "|A| <o |UNIV::'a set|" 
    using assms finite_ordLess_infinite2 var_TT_infinite by blast
  thus ?thesis using that 
    using assms ex_new_if_finite var_TT_infinite by blast
qed
 
(* .. then the induction principle statement: *)
theorem subtyping_fresh_induct_param[consumes 2, case_names SA_TTop SA_TVar_Refl SA_TVar_Trans SA_TArr SA_TAll SA_TRec]:
  fixes T :: "'a::{large_G,var_TT} TT" and K :: "'p \<Rightarrow> 'a set"
  assumes fin: "\<forall>\<rho>. finite (K \<rho>)" and Gam: "\<Gamma> \<turnstile> U <: T" 
    and TTop: "\<And>\<Gamma> T \<rho>. \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T \<Longrightarrow> \<phi> \<Gamma> T TTop \<rho>"
    and TVar_Refl: "\<And>\<Gamma> X \<rho>. \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow> X \<in> fst ` set \<Gamma> \<Longrightarrow> \<phi> \<Gamma> (TVar X) (TVar X) \<rho>"
    and TVar_Trans: "\<And>X U \<Gamma> T \<rho>. (X, U) \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> U <: T \<Longrightarrow> (\<And>\<rho>. \<phi> \<Gamma> U T \<rho>) \<Longrightarrow> \<phi> \<Gamma> (TVar X) T \<rho>"
    and TArr: "\<And>\<Gamma> T1 S1 S2 T2 \<rho>.
            \<Gamma> \<turnstile> T1 <: S1 \<Longrightarrow> (\<And>\<rho>. \<phi> \<Gamma> T1 S1 \<rho>) \<Longrightarrow> \<Gamma> \<turnstile> S2 <: T2 \<Longrightarrow> (\<And>\<rho>. \<phi> \<Gamma> S2 T2 \<rho>) \<Longrightarrow> \<phi> \<Gamma> (TArr S1 S2) (TArr T1 T2) \<rho>"
    and TAll: "\<And>\<Gamma> T1 S1 x S2 T2 \<rho>.
            (* the only difference from subtyping.induct: *)x \<notin> K \<rho> \<Longrightarrow>
            \<Gamma> \<turnstile> T1 <: S1 \<Longrightarrow>
            (\<And>\<rho>. \<phi> \<Gamma> T1 S1 \<rho>) \<Longrightarrow> x \<notin> fst ` set \<Gamma> \<Longrightarrow> (x, T1) # \<Gamma> \<turnstile> S2 <: T2 \<Longrightarrow> (\<And>\<rho>. \<phi> ((x, T1) # \<Gamma>) S2 T2 \<rho>) \<Longrightarrow> \<phi> \<Gamma> (TAll x S1 S2) (TAll x T1 T2) \<rho>"
    and TRec: "\<And>\<Gamma> X Y \<rho>. \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow>
                  \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T TRec X \<Longrightarrow>
                  labels X \<subseteq> labels Y \<Longrightarrow>
                  (\<And>x T. (x, T) \<in>\<in> Y \<Longrightarrow> \<exists>S. (x, S) \<in>\<in> X \<and> \<Gamma> \<turnstile> S <: T \<and> (\<forall>\<rho>. \<phi> \<Gamma> S T \<rho>)) \<Longrightarrow> \<phi> \<Gamma> (TRec X) (TRec Y) \<rho>"
  shows "All (\<phi> \<Gamma> U T)" 
proof-    
  {fix \<rho>::'p 
   from Gam have "cl \<phi> \<Gamma> U T \<rho>"  
   proof(induction arbitrary: \<rho> rule: subtyping.induct)
     case (SA_TAll \<Gamma> T1 S1 x S2 T2 \<rho>) note cs = this
     show ?case proof (intro clI, safe) 
       fix f::"'a \<Rightarrow> _" assume f: "bij f" "finite (supp f)"
       have x: "x \<notin> FFVars S1 \<union> FFVars T1 \<union> fst ` set \<Gamma>" 
         using cs(2) subtyping_wf_type[OF cs(1)] unfolding wf_type_FFVars by auto
       let ?A = "{x} \<union> vars_ctxt \<Gamma> \<union> FFVars S1 \<union> FFVars S2 \<union> 
        FFVars T1 \<union> FFVars T2 \<union> imsupp f \<union> K \<rho>"
       have "finite ?A" 
       using finite_FFVars f fin unfolding imsupp_def by (intro finite_UnI) auto
       then obtain x' where x': "x' \<notin> ?A" using finite_obtains by metis
       define S2' where S2': "S2' = vvsubst (swap x x') S2" 
       define T2' where T2': "T2' = vvsubst (swap x x') T2" 
       have 0: "TAll x S1 S2 = TAll x' S1 S2'" "TAll x T1 T2 = TAll x' T1 T2'" 
         unfolding S2' T2' TAll_inject using x'
         by (auto simp: vusubst_def supp_id_upd swap_def intro!: vvsubst_cong)
       have "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma>" using cs(1) using subtyping_wf_ctxt by blast
       hence [simp]: "swap_ctxt x x' \<Gamma> = \<Gamma>" using swap_wf_ctxt_idle x x' by auto
       have [simp]: "f x' = x'" using x' unfolding imsupp_def supp_def by auto
       have cl_cl: "\<And> \<rho>. cl (cl \<phi>) ((x, T1) # \<Gamma>) S2 T2 \<rho>" using cs(5) unfolding cl_cl .
       show "\<phi> (map (map_prod f (vvsubst f)) \<Gamma>) (vvsubst f (TAll x S1 S2))
             (vvsubst f (TAll x T1 T2)) \<rho>" unfolding 0
         using x x' f apply auto apply(rule TAll) apply (auto simp: image_def)
           subgoal apply(auto simp: subtyping_vvsubst cs) .
           subgoal apply(rule clE[OF cs(4)]) apply auto .
           subgoal unfolding imsupp_def supp_def apply auto .
           subgoal using subtyping_vvsubst[OF subtyping_vvswap[OF cs(3), of x x'] f]
             apply (auto simp: S2'[symmetric] T2'[symmetric]) .
           subgoal  
             using clE[OF clE_vvswap[OF cl_cl, of x x'] f]
             apply (auto simp: S2'[symmetric] T2'[symmetric]) .
           done
        qed    
   next
     case (SA_TRec \<Gamma> X Y \<rho>)
     thus ?case apply(intro clI) 
     apply(auto intro!: assms vvsubst_wf_ctxt vvsubst_wf_type 
               subtyping_vvsubst clE[of \<phi>]
           simp: lfset_set1_map[unfolded o_def fun_eq_iff, simplified, rule_format]
           lfin_map_lfset
     )
     apply(drule vvsubst_wf_type) apply auto 
     by (fastforce intro!: subtyping_vvsubst)
   qed(intro clI, force intro!: assms vvsubst_wf_ctxt vvsubst_wf_type 
               subtyping_vvsubst clE[of \<phi>])+ 
  }
  from cl_ext[OF this] show ?thesis by auto
qed

theorem subtyping_fresh_induct[consumes 2, case_names SA_TTop SA_TVar_Refl SA_TVar_Trans SA_TArr SA_TAll SA_TRec]:
  assumes "finite K" "\<Gamma> \<turnstile> U <: T"
    and "\<And>\<Gamma> T. \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T \<Longrightarrow> \<phi> \<Gamma> T TTop"
    and "\<And>\<Gamma> X. \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow> X \<in> fst ` set \<Gamma> \<Longrightarrow> \<phi> \<Gamma> (TVar X) (TVar X)"
    and "\<And>X U \<Gamma> T. (X, U) \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> U <: T \<Longrightarrow> \<phi> \<Gamma> U T \<Longrightarrow> \<phi> \<Gamma> (TVar X) T"
    and "\<And>\<Gamma> T1 S1 S2 T2.
            \<Gamma> \<turnstile> T1 <: S1 \<Longrightarrow> \<phi> \<Gamma> T1 S1 \<Longrightarrow> \<Gamma> \<turnstile> S2 <: T2 \<Longrightarrow> \<phi> \<Gamma> S2 T2 \<Longrightarrow> \<phi> \<Gamma> (TArr S1 S2) (TArr T1 T2)"
    and "\<And>\<Gamma> T1 S1 x S2 T2.
            (* the only difference from subtyping.induct: *)x \<notin> K \<union> vars_ctxt \<Gamma> \<union> FFVars S1 \<union> FFVars T1 \<Longrightarrow>
            \<Gamma> \<turnstile> T1 <: S1 \<Longrightarrow>
            \<phi> \<Gamma> T1 S1 \<Longrightarrow> x \<notin> fst ` set \<Gamma> \<Longrightarrow> (x, T1) # \<Gamma> \<turnstile> S2 <: T2 \<Longrightarrow> \<phi> ((x, T1) # \<Gamma>) S2 T2 \<Longrightarrow> \<phi> \<Gamma> (TAll x S1 S2) (TAll x T1 T2)"
    and "\<And>\<Gamma> X Y. \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<Longrightarrow>
                  \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T TRec X \<Longrightarrow>
                  labels X \<subseteq> labels Y \<Longrightarrow>
                  (\<And>x T. (x, T) \<in>\<in> Y \<Longrightarrow> \<exists>S. (x, S) \<in>\<in> X \<and> \<Gamma> \<turnstile> S <: T \<and> \<phi> \<Gamma> S T) \<Longrightarrow> \<phi> \<Gamma> (TRec X) (TRec Y)"
  shows "\<phi> \<Gamma> U T"
proof -
  from \<open>finite K\<close> have "\<forall>\<rho>. finite (case \<rho> of (\<Gamma>, U, T) \<Rightarrow> K \<union> vars_ctxt \<Gamma> \<union> FFVars U \<union> FFVars T)"
    by auto
  from this \<open>\<Gamma> \<turnstile> U <: T\<close> have "\<forall>\<rho>. \<rho> = (\<Gamma>, U, T) \<longrightarrow> \<phi> \<Gamma> U T"
    by (induct rule: subtyping_fresh_induct_param) (auto simp: assms(3-8))
  then show ?thesis by simp
qed

theorem subtyping_fresh_cases[consumes 2, case_names SA_TTop SA_TVar_Refl SA_TVar_Trans SA_TArr SA_TAll SA_TRec]:
  fixes P Q :: "'a :: {large_G, var_TT} TT"
  assumes "finite K" "\<Delta> \<turnstile> P <: Q"
  obtains
    \<Gamma> :: "('a \<times> 'a TT) list" and T :: "'a TT" where "\<Delta> = \<Gamma>" and "P = T" and "Q = TTop" and "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma>"
      and "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T"
    | \<Gamma> :: "('a \<times> 'a TT) list" and X :: "'a" where "\<Delta> = \<Gamma>" and "P = TVar X" and "Q = TVar X" and
        "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma>" and "X \<in> fst ` set \<Gamma>"
    | X :: "'a" and U :: "'a TT" and \<Gamma> :: "('a \<times> 'a TT) list" and T :: "'a TT" where "\<Delta> = \<Gamma>" and
        "P = TVar X" and "Q = T" and "(X, U) \<in> set \<Gamma>" and "\<Gamma> \<turnstile> U <: T"
    | \<Gamma> :: "('a \<times> 'a TT) list" and T1 :: "'a TT" and S1 :: "'a TT" and S2 :: "'a TT" and
        T2 :: "'a TT" where "\<Delta> = \<Gamma>" and "P = TArr S1 S2" and "Q = TArr T1 T2" and
        "\<Gamma> \<turnstile> T1 <: S1" and "\<Gamma> \<turnstile> S2 <: T2"
    | \<Gamma> :: "('a \<times> 'a TT) list" and T1 :: "'a TT" and S1 :: "'a TT" and x :: "'a" and S2 :: "'a TT" and
        T2 :: "'a TT" where "x \<notin> K \<union> vars_ctxt \<Gamma> \<union> FFVars S1 \<union> FFVars T1" and "\<Delta> = \<Gamma>" and
        "P = TAll x S1 S2" and "Q = TAll x T1 T2" and "\<Gamma> \<turnstile> T1 <: S1" and 
        "x \<notin> fst ` set \<Gamma>" and "(x, T1) # \<Gamma> \<turnstile> S2 <: T2"
    | \<Gamma> :: "('a \<times> 'a TT) list" and X :: "(nat, 'a TT) lfset" and Y :: "(nat, 'a TT) lfset" where "\<Delta> = \<Gamma>"
        and "P = TRec X" and "Q = TRec Y" and "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma>" and "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T TRec X" and "labels X \<subseteq> labels Y" and
        "\<And>x T. (x, T) \<in>\<in> Y \<Longrightarrow> \<exists>S. (x, S) \<in>\<in> X \<and> \<Gamma> \<turnstile> S <: T"
using assms proof (atomize_elim, induct rule: subtyping_fresh_induct)
  case (SA_TRec \<Gamma> X Y)
  then show ?case by auto
qed metis+

declare TAll_inject[simp,induct_simp]
inductive_cases
  subtyping_TAllE: "\<Gamma> \<turnstile> TAll x T U <: TAll x T' U'"

theorem subtyping_fresh_TAllLE[elim]:
  fixes T U S :: "'a::{large_G,var_TT} TT"
  assumes "finite K" "\<Gamma> \<turnstile> TAll x T U <: S"
  obtains "S = TTop" and "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma>" and "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T TAll x T U"
  | T1 :: "'a TT" and S1 :: "'a TT" and y :: "'a" and S2 :: "'a TT" and T2 :: "'a TT" where
    "y \<notin> K \<union> vars_ctxt \<Gamma> \<union> FFVars S1 \<union> FFVars T1" and "TAll x T U = TAll y S1 S2" and
    "S = TAll y T1 T2" and "\<Gamma> \<turnstile> T1 <: S1" and "y \<notin> fst ` set \<Gamma>" and "(y, T1) # \<Gamma> \<turnstile> S2 <: T2"
  using assms by (rule subtyping_fresh_cases) (auto split: if_splits)

lemma REFLEXIVITY:
  assumes  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T" "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma>"
  shows "\<Gamma> \<turnstile> T <: T"
proof -
  have "\<forall>\<Gamma>. |fst ` set \<Gamma>| <o bound(any :: 'a)" by auto
  then have "\<forall>\<Gamma>. \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T \<longrightarrow> \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma> \<longrightarrow> \<Gamma> \<turnstile> T <: T"
    by (induct T rule: user_TT_fresh_induct_param_UNIV)
      (force simp: lfin_values wf_type_FFVars Diff_single_insert WF_Cons)+
  with assms show ?thesis by blast
qed

definition "ctxt_weaken \<Gamma> \<Delta> = (\<forall>x T. (x, T) \<in> set \<Gamma> \<longrightarrow> (x, T) \<in> set \<Delta>)"

lemma ctxt_weakenE[elim]: "ctxt_weaken \<Gamma> \<Delta> \<Longrightarrow> (x, T) \<in> set \<Gamma> \<Longrightarrow> (x, T) \<in> set \<Delta>"
  unfolding ctxt_weaken_def by blast

lemma wf_type_ctxt_weaken[elim]: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T \<Longrightarrow> ctxt_weaken \<Gamma> \<Delta> \<Longrightarrow> \<Delta> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T"
  by (force simp: ctxt_weaken_def wf_type_FFVars)

lemma wf_type_replace: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T \<Longrightarrow> list_all2 (rel_prod (=) top) \<Gamma> \<Delta> \<Longrightarrow> \<Delta> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T"
  by (force simp: wf_type_FFVars list.in_rel)

lemma wf_ctxt_replace[elim]:
  "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Delta> @ (x, T) # \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>T T' \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Delta> @ (x, T') # \<Gamma>"
  by (induct \<Delta>) (auto elim!: wf_ctxtE wf_type_replace simp: list_all2_append image_Un rev_image_eqI
    intro!: list_all2_refl)

lemma subtyping_ctxt_weaken:
  assumes "\<Gamma> \<turnstile> T <: U" "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Delta>" "ctxt_weaken \<Gamma> \<Delta>"
  shows "\<Delta> \<turnstile> T <: U"
proof -
  have "\<forall>\<Delta>. finite (fst ` set \<Delta>)" by auto
  from this \<open>\<Gamma> \<turnstile> T <: U\<close> have "\<forall>\<Delta>. \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Delta> \<longrightarrow> ctxt_weaken \<Gamma> \<Delta> \<longrightarrow> \<Delta> \<turnstile> T <: U"
  proof (induct \<Gamma> T U rule: subtyping_fresh_induct_param)
    case (SA_TAll \<Gamma> T1 S1 x S2 T2 \<Delta>)
    from SA_TAll(3)[of \<Delta>] SA_TAll(6)[rule_format, of "(x, T1) # \<Delta>", OF wf_ctxt.intros(2)] SA_TAll(1,2,4,5)
    show ?case by (auto simp: ctxt_weaken_def)
  qed force+
  with assms(2,3) show ?thesis by blast
qed

lemma prepend_ctxt_weaken: "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Delta> @ \<Gamma> \<Longrightarrow> ctxt_weaken \<Gamma> (\<Delta> @ \<Gamma>)"
  by (induct \<Delta> arbitrary: \<Gamma>) (auto simp: ctxt_weaken_def)

lemma WEAKENING: "\<Gamma> \<turnstile> S <: T \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Delta> @ \<Gamma> \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> S <: T"
  using subtyping_ctxt_weaken prepend_ctxt_weaken by blast

lemma wf_ctxt_suffix: "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Delta> @ \<Gamma> \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma>"
  by (induct \<Delta> arbitrary: \<Gamma> rule: rev_induct) (auto elim: wf_ctxtE)

lemma narrowing_from_transitivity:
  assumes trans: "(\<And>\<Gamma> S T. \<Gamma> \<turnstile> S <: Q \<Longrightarrow> \<Gamma> \<turnstile> Q <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T)"
  shows "\<Delta> @ (x, Q) # \<Gamma> \<turnstile> M <: N \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ (x, P) # \<Gamma> \<turnstile> M <: N"
proof (induct "\<Delta> @ (x, Q) # \<Gamma>" M N arbitrary: \<Delta> rule: subtyping.induct)
    case (SA_TVar_Trans _ _ T)
    then show ?case
      by (auto intro!: WEAKENING[of "(x, P) # \<Gamma>" "TVar x" Q \<Delta>, THEN trans, of T]
        subtyping.SA_TVar_Trans[rotated, OF WEAKENING[of \<Gamma> P Q "[(x, P)]"], simplified]
        dest:  subtyping_wf_ctxt[THEN wf_ctxt_suffix[of \<Delta>]] elim!: wf_ctxtE)
qed (auto 5 2 elim!: wf_type_replace intro!: list_all2_refl
  simp: list_all2_append subtyping_wf_type, fastforce?)

lemma TAll_rename: "y \<notin> FFVars U \<Longrightarrow> TAll x T U = TAll y T (vvsubst (swap x y) U)"
  unfolding TAll_inject
  by (auto simp: FFVars_vvsubst supp_id_upd swap_def vusubst_def intro!: vvsubst_cong)

lemma vvswap_id: "x \<notin> FFVars R \<Longrightarrow> y \<notin> FFVars R \<Longrightarrow> vvswap x y R = R"
  by (auto simp: swap_def intro: trans[OF vvsubst_cong vvsubst_id])

lemma swap_ctxt_id: "x \<notin> vars_ctxt \<Gamma> \<Longrightarrow> y \<notin> vars_ctxt \<Gamma> \<Longrightarrow> swap_ctxt x y \<Gamma> = \<Gamma>"
  by (induct \<Gamma>) (auto simp: vvswap_id)

lemma subtyping_vvswap_fresh:
  assumes "(x, R) # \<Gamma> \<turnstile> T <: U"
  and fresh: "x \<notin> vars_ctxt \<Gamma> \<union> FFVars R" "y \<notin> vars_ctxt \<Gamma> \<union> FFVars R"
  shows "(y, R) # \<Gamma> \<turnstile> vvsubst (swap x y) T <: vvsubst (swap x y) U"
  using subtyping_vvswap[OF assms(1), of x y] fresh
  by (auto simp: swap_def vvswap_id swap_ctxt_id)

theorem TRANSITIVITY:
  assumes "\<Gamma> \<turnstile> S <: Q" "\<Gamma> \<turnstile> Q <: T"
  shows "\<Gamma> \<turnstile> S <: T"
proof -
  have bd: "\<forall>\<rho>. |case \<rho> of (\<Gamma>::'a ctxt, S::'a TT, T::'a TT) \<Rightarrow> vars_ctxt \<Gamma> \<union> FFVars S \<union> FFVars T| <o bound(any::'a)"
    by auto
  have "\<forall>\<rho>. case \<rho> of (\<Gamma>, S, T) \<Rightarrow> \<Gamma> \<turnstile> S <: Q \<longrightarrow> \<Gamma> \<turnstile> Q <: T \<longrightarrow> \<Gamma> \<turnstile> S <: T"
  proof (rule user_TT_fresh_induct_param_UNIV[OF bd], safe, goal_cases TVar TArr TAll TRec)
    case (TVar y \<Gamma> S T)
    from TVar show ?case by (induct \<Gamma> S "TVar y") auto
  next
    case (TArr T1 U1 \<Gamma> S T)
    from TArr(3,4) show ?case
      by (induct \<Gamma> S "TArr T1 U1") (auto 0 4 simp: wf_type_FFVars image_iff Bex_def
        dest: subtyping_wf_type elim: TArr(1,2)[rule_format])
  next
    case (TAll y T1 U1 \<Gamma> S T)
    have "finite {y}" by auto
    from this TAll(7,8,3-6) show ?case
    proof (induct \<Gamma> S "TAll y T1 U1" rule: subtyping_fresh_induct)
      note FFVars_vvsubst[simp]
      case (SA_TAll \<Gamma> T1' L1 x L2 U1')
      then have [simp]: "U1 = vvswap x y U1'" "T1' = T1" "x \<noteq> y" and
        [simplified, simp]: "x \<notin> FFVars U1" "x \<notin> FFVars L1" "x \<notin> FFVars T1'"
        "\<And>U. (x, U) \<notin> set \<Gamma>" "\<And>y U. (y, U) \<in> set \<Gamma> \<Longrightarrow> x \<notin> FFVars U"
        "y \<notin> FFVars L1" "y \<notin> FFVars L2" "y \<notin> FFVars T" "y \<notin> FFVars U1'"
        "\<And>U. (y, U) \<notin> set \<Gamma>" "\<And>z U. (z, U) \<in> set \<Gamma> \<Longrightarrow> y \<notin> FFVars U"
        by (auto 0 2 simp: image_iff vusubst_def supp_id_upd swap_def intro!: vvsubst_cong)
      from SA_TAll(9) show ?case
      proof (elim subtyping_fresh_TAllLE[rotated, where K = "{x,y}"])
        assume "T = TTop" "\<turnstile>\<^sub>w\<^sub>f\<^sub>T \<Gamma>"
        then show "\<Gamma> \<turnstile> TAll x L1 L2 <: T"
        using SA_TAll(2,4,5) subtyping_wf_type by blast
      next
        fix R1 S1 z S2 R2
        assume [simp]: "T = TAll z R1 R2" and "TAll y T1 U1 = TAll z S1 S2"
           and "z \<notin> {x,y} \<union> (fst ` set \<Gamma> \<union> UNION (snd ` set \<Gamma>) FFVars) \<union> FFVars S1 \<union> FFVars R1"
        then have [simp]: "S1 = T1" "S2 = vvswap y z U1" "y \<notin> FFVars S2" "z \<notin> FFVars U1" and
          [simplified, simp]: "z \<noteq> x" "z \<noteq> y" "\<And>U. (z, U) \<notin> set \<Gamma>" "z \<notin> FFVars S1" "z \<notin> FFVars R1"
          "\<And>y U. (y, U) \<in> set \<Gamma> \<Longrightarrow> z \<notin> FFVars U"
          by (auto 0 2 simp: image_iff vusubst_def supp_id_upd swap_def intro!: vvsubst_cong)
        assume *: "\<Gamma> \<turnstile> R1 <: S1" "(z, R1) # \<Gamma> \<turnstile> S2 <: R2"
        have [simp]: "y \<notin> FFVars R2" "y \<notin> FFVars R1" "y \<notin> FFVars T1" "x \<notin> FFVars R1"
          using subtyping_wf_type[OF SA_TAll(2)] subtyping_wf_type[OF *(1)] subtyping_wf_type[OF *(2)]
          unfolding wf_type_FFVars by force+
        note IH = TAll(1,2)[rule_format, simplified]
        { from SA_TAll(5) *(1) have "(y, R1) # \<Gamma> \<turnstile> vvswap x y L2 <: vvswap x y U1'"
            by (auto elim!: IH(1) intro!: subtyping_vvswap_fresh
              intro: narrowing_from_transitivity[where \<Delta> = "[]", simplified])
          moreover
          assume "(z, R1) # \<Gamma> \<turnstile> vvswap y z (vvswap x y U1') <: R2"
          then have "(y, R1) # \<Gamma> \<turnstile> vvswap x y U1' <: vvswap z y R2"
            by (auto dest!: subtyping_vvswap_fresh[of z _ _ _ _ y] simp: vvsubst_o[symmetric, of "swap z y"])
          ultimately have "(y, R1) # \<Gamma> \<turnstile> vvswap x y L2 <: vvswap z y R2" by (rule IH(2))
        }
        with * show "\<Gamma> \<turnstile> TAll x L1 L2 <: T"
          by (auto simp: TAll_rename[of y _ x] TAll_rename[of y _ z] SA_TAll(2)[simplified]
            elim!: TAll(1)[rule_format, simplified] TAll(2)[rule_format])
      qed simp
    qed (meson contra_subsetD subtyping.SA_TVar_Trans subtyping_wf_type wf_type_FFVars)
  next
    case (TRec X \<Gamma> S T)
    from TRec(2,3) show ?case
    proof (induct \<Gamma> S "TRec X")
      case (SA_TRec \<Gamma> Y)
      { fix Z
        assume "T = TRec Z" and lab: "labels X \<subseteq> labels Z"
          and  XZ: "\<And>x T. (x, T) \<in>\<in> Z \<Longrightarrow> \<exists>S. (x, S) \<in>\<in> X \<and> \<Gamma> \<turnstile> S <: T"
        have "\<Gamma> \<turnstile> TRec Y <: T" unfolding \<open>T = TRec Z\<close>
        proof
          fix x T
          assume "(x, T) \<in>\<in> Z"
          with XZ obtain S where "(x, S) \<in>\<in> X" "\<Gamma> \<turnstile> S <: T" by blast
          with SA_TRec(4)[of x S] show "\<exists>S. (x, S) \<in>\<in> Y \<and> \<Gamma> \<turnstile> S <: T"
            by (auto simp: lfin_values elim!: TRec(1)[rule_format, rotated])
        qed (auto simp: subset_trans[OF SA_TRec(3) lab] SA_TRec(1,2))
      }
      with SA_TRec(5,1-3) show ?case
        by (elim subtyping_TRecLE) (auto simp: image_iff Bex_def)
    qed auto
  qed
  with assms show ?thesis by blast
qed

end
