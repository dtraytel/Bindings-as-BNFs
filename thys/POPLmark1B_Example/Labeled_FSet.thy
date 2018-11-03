theory Labeled_FSet
  imports "../Prelim" "HOL-Library.FSet"
begin

abbreviation nonrep_pair :: "'a \<times> 'b \<Rightarrow> bool" where "nonrep_pair _ \<equiv> True"
abbreviation nonrep_fset :: "'a fset \<Rightarrow> bool" where "nonrep_fset _ \<equiv> True"
definition nonrep_lfset :: "('a \<times> 'b) fset \<Rightarrow> bool" where
  "nonrep_lfset X = (nonrep_fset X \<and> (\<forall>x \<in> fset X. nonrep_pair x) \<and>
     (\<forall>x \<in> fset X. \<forall>y \<in> fset X. x \<noteq> y \<longrightarrow> Basic_BNFs.fsts x \<inter> Basic_BNFs.fsts y = {}))"
  
lemma nonrep_lfset_alt:
  "nonrep_lfset X = (\<forall>a b c. (a, b) |\<in>| X \<longrightarrow>  (a, c) |\<in>| X \<longrightarrow> b = c)"
  unfolding nonrep_lfset_def prod_set_defs fmember.rep_eq by fastforce

typedef ('a, 'b) G = "UNIV :: ('a \<times> 'b) fset set" by auto
copy_bnf ('a, 'b) G
setup_lifting type_definition_G

lemma map_G_transfer[transfer_rule]:
  "rel_fun (=) (rel_fun (=) (rel_fun (pcr_G (=) (=)) (pcr_G (=) (=)))) (\<lambda>f g. (|`|) (map_prod f g)) map_G"
  by (tactic \<open>Local_Defs.unfold_tac @{context}
      [BNF_Def.bnf_of @{context} @{type_name G} |> the |> BNF_Def.map_def_of_bnf]\<close>)
    (simp add: rel_fun_def pcr_G_def cr_G_def prod.rel_eq fset.rel_eq relcompp_apply Abs_G_inverse)

lift_definition nonrep_G :: "('a, 'b) G \<Rightarrow> bool" is nonrep_lfset .

lemma nonrep_G_map: "bij f \<Longrightarrow> nonrep_G x \<Longrightarrow> nonrep_G (map_G f g x)"
  by (transfer fixing: f g)
    (force simp: nonrep_lfset_alt map_prod_def fimage_iff the_inv_f_f bij_is_inj
    dest!: bij_the_inv_revert[of f, THEN iffD2, rotated])

lemma nonrep_G_map_fst_snd:
  "nonrep_G (map_G f fst x) \<Longrightarrow> nonrep_G (map_G f snd x) \<Longrightarrow> nonrep_G (map_G f id x)"
  apply transfer
  apply (auto simp: nonrep_lfset_alt map_prod_def image_iff split_beta fBex.rep_eq fmember.rep_eq)
  by (metis fst_conv snd_conv)+

lemma nonrep_G_map_fst_snd_bij:
  "bij f \<Longrightarrow> nonrep_G (map_G f fst x) \<Longrightarrow> nonrep_G (map_G f snd x) \<Longrightarrow> nonrep_G x"
  apply (transfer fixing: f)
  apply (auto simp: nonrep_lfset_alt map_prod_def image_iff split_beta fBex.rep_eq fmember.rep_eq)
  by (metis fst_conv snd_conv)+

class large_G =
  fixes dummy :: 'a
  assumes large_G: "bd_G \<le>o |UNIV :: 'a set|"

instantiation nat :: large_G begin
instance proof
qed (metis Card_order_iff_ordLeq_card_of G.bd_card_order card_order_on_Card_order)
end

instantiation prod ::  (type, large_G) large_G begin
instance proof
qed (subst UNIV_prod, auto simp only: intro!: ordLeq_transitive[OF large_G card_of_Times2])
end

typedef ('a, 'b) lfset = "{x :: ('a :: large_G, 'b) G . nonrep_G x}"
  unfolding mem_Collect_eq
  by transfer (auto simp: nonrep_lfset_alt)

definition map_lfset :: "('a :: large_G \<Rightarrow> 'a' :: large_G) \<Rightarrow> ('b \<Rightarrow> 'b') \<Rightarrow> ('a, 'b) lfset \<Rightarrow> ('a', 'b') lfset" where
  "map_lfset f g = Abs_lfset o map_G f g o Rep_lfset"

definition labels :: "('a :: large_G, 'b) lfset \<Rightarrow> 'a set" where
  "labels = set1_G o Rep_lfset"

definition "values" :: "('a :: large_G, 'b) lfset \<Rightarrow> 'b set" where
  "values = set2_G o Rep_lfset"

definition rel_lfset :: "('a :: large_G \<Rightarrow> 'a :: large_G) \<Rightarrow> ('b \<Rightarrow> 'b' \<Rightarrow> bool) \<Rightarrow> ('a, 'b) lfset \<Rightarrow> ('a, 'b') lfset \<Rightarrow> bool" where
  "rel_lfset f S = BNF_Def.vimage2p Rep_lfset Rep_lfset (rel_G (Grp f) S)"

theorem lfset_map_id: "map_lfset id id = id"
  unfolding map_lfset_def G.map_id fun_eq_iff o_apply Rep_lfset_inverse id_apply
  by (rule allI, rule refl)

theorem lfset_map_comp: "bij u \<Longrightarrow> map_lfset (v o u) (f o g) = map_lfset v f o map_lfset u g"
  by (simp only: map_lfset_def fun_eq_iff o_apply simp_thms G.map_comp
    Abs_lfset_inverse[unfolded mem_Collect_eq] nonrep_G_map Rep_lfset[unfolded mem_Collect_eq])

theorem lfset_set1_map: "bij u \<Longrightarrow> labels o map_lfset u g = image u o labels"
  by (simp only: labels_def map_lfset_def fun_eq_iff o_apply simp_thms G.set_map
    Abs_lfset_inverse[unfolded mem_Collect_eq] nonrep_G_map Rep_lfset[unfolded mem_Collect_eq])

theorem lfset_set2_map: "bij u \<Longrightarrow> values o map_lfset u g = image g o values"
  by (simp only: values_def map_lfset_def fun_eq_iff o_apply simp_thms G.set_map
    Abs_lfset_inverse[unfolded mem_Collect_eq] nonrep_G_map Rep_lfset[unfolded mem_Collect_eq])

theorem lfset_map_cong:
  assumes "\<And>a. a \<in> labels p \<Longrightarrow> u a = v a" "\<And>a. a \<in> values p \<Longrightarrow> g a = h a"
  shows "map_lfset u g p = map_lfset v h p"
  by (simp only: map_lfset_def o_apply labels_def values_def assms cong: G.map_cong)

theorem lfset_set_bd: "|labels p| \<le>o bd_G"  "|values p| \<le>o bd_G"
  unfolding labels_def values_def o_apply by (rule G.set_bd)+

theorem lfset_rel_eq:
  "rel_lfset id ((=)) = ((=))"
  unfolding rel_lfset_def vimage2p_def eq_alt[symmetric] G.rel_eq Rep_lfset_inject ..

theorem lfset_in_rel:
  "bij f \<Longrightarrow> rel_lfset f R x y = (\<exists>z. values z \<subseteq> {(x,y). R x y} \<and> map_lfset id fst z = x \<and> map_lfset f snd z = y)"
  unfolding rel_lfset_def vimage2p_def G.in_rel
  apply safe
  subgoal for z
    apply (subgoal_tac "nonrep_G (map_G fst id z)")
     apply (rule exI[of _ "Abs_lfset (map_G fst id z)"])
     apply (cases x; cases y)
     apply (auto simp: map_lfset_def values_def Grp_def
        Abs_lfset_inverse Rep_lfset[simplified] nonrep_G_map G.set_map G.map_comp
        G.map_comp[of "inv f" id snd snd, simplified, symmetric]
        intro!: Abs_lfset_inject[THEN iffD2] G.map_cong nonrep_G_map_fst_snd
        arg_cong[of _ _ nonrep_G, OF G.map_cong[of _ _ fst "inv f o snd" snd snd, OF refl], THEN iffD2]
        elim!: arg_cong[of _ _ nonrep_G, THEN iffD1, rotated])
    done
  subgoal for z
    apply (rule exI[of _ "map_G (\<lambda>x. (x, f x)) id (Rep_lfset z)"])
    apply (auto simp: G.set_map G.map_comp Grp_def values_def map_lfset_def Abs_lfset_inverse Rep_lfset[simplified] nonrep_G_map
      intro!: G.map_cong)
    done
  done

theorem lfset_rel_compp_le:
  "rel_lfset f R OO rel_lfset g S \<le> rel_lfset (g o f) (R OO S)"
  unfolding rel_lfset_def G.rel_compp Grp_o
  by (rule vimage2p_relcompp_mono[OF order_refl])
(*
  unfolding vimage2p_Grp fun_eq_iff relcompp_apply conversep_iff eqTrueI[OF UNIV_I] simp_thms
  apply (safe elim!: GrpE)
  subgoal premises prems for x y _ _ z
  proof (cases z rule: Rep_lfset_cases[unfolded mem_Collect_eq, case_names nonrep_G Rep_lfset])
    case nonrep_G
    with prems(2,5) Rep_lfset[of x] show ?case

      apply (auto simp: G.in_rel Grp_def) find_theorems nonrep_G sorry
  next
    case (Rep_lfset x)
    with prems show ?thesis by (auto simp: Grp_def)
  qed
  done
*)

(* locale+interpretation as a trick to get automatic proofs and replace new constants
   by existing ones afterwards *)
locale AUX
lift_bnf (in AUX) (dead 'a :: large_G, aux_set_lfset: 'b) lfset [wits: "Abs_G {||} :: ('a :: large_G, 'b) G"]
  for map: aux_map_lfset rel: aux_rel_lfset
  by (auto simp add: nonrep_G.abs_eq nonrep_lfset_def Abs_G_inverse set2_G_def
    intro: nonrep_G_map nonrep_G_map_fst_snd_bij)

(*FIXME for J: problem with tactic in datatype and primrec otherwise*)
definition [simp]: "map_lfset_id = map_lfset id"
definition [simp]: "rel_lfset_id = rel_lfset id"

interpretation AUX
  rewrites "AUX.aux_map_lfset = map_lfset_id" and "AUX.aux_rel_lfset = rel_lfset_id" and "AUX.aux_set_lfset = values"
  by (tactic \<open>Local_Defs.unfold_tac @{context} (@{thms values_def map_lfset_def rel_lfset_def map_lfset_id_def rel_lfset_id_def eq_alt[symmetric]} @
    maps (fn f => BNF_Def.bnf_of @{context} @{type_name lfset} |> the |> f) [BNF_Def.set_defs_of_bnf,
      single o BNF_Def.map_def_of_bnf, single o BNF_Def.rel_def_of_bnf])\<close>) (rule refl)+

context begin

qualified definition "Rep = Rep_G o Rep_lfset"
qualified definition "Abs = Abs_lfset o Abs_G"

lemma type_definition_lfset:
  "type_definition Rep Abs {X. nonrep_lfset X}"
  by unfold_locales
    (auto simp: Rep_def Abs_def Rep_lfset[unfolded mem_Collect_eq] nonrep_G.abs_eq[symmetric]
      Rep_G_inverse Rep_lfset_inverse Abs_lfset_inverse Abs_G_inverse)

setup_lifting type_definition_lfset

lemma map_lfset_id_transfer[transfer_rule]:
  "rel_fun (=) (rel_fun (pcr_lfset (=) (=)) (pcr_lfset (=) (=))) (\<lambda>g. fimage (map_prod id g)) (map_lfset id)"
  unfolding rel_fun_def pcr_lfset_def cr_lfset_def prod.rel_eq fset.rel_eq eq_OO map_lfset_def Rep_def o_apply
  by (subst Abs_lfset_inverse; simp add: Rep_lfset[simplified] nonrep_G_map)
    (tactic \<open>Local_Defs.unfold_tac @{context}
      [BNF_Def.bnf_of @{context} @{type_name G} |> the |> BNF_Def.map_def_of_bnf]\<close>, simp add: Abs_G_inverse)

lemma labels_transfer[transfer_rule]:
  "rel_fun (pcr_lfset (=) (=)) (rel_set (=)) (image fst o fset) labels"
  unfolding rel_fun_def pcr_lfset_def cr_lfset_def prod.rel_eq fset.rel_eq eq_OO labels_def Rep_def o_apply
  by (tactic \<open>Local_Defs.unfold_tac @{context}
    (BNF_Def.bnf_of @{context} @{type_name G} |> the |> BNF_Def.set_defs_of_bnf)\<close>)
    (auto simp: rel_fun_def rel_set_eq elim: image_eqI[rotated])

lemma values_transfer[transfer_rule]:
  "rel_fun (pcr_lfset (=) (=)) (rel_set (=)) (image snd o fset) values"
  unfolding rel_fun_def pcr_lfset_def cr_lfset_def prod.rel_eq fset.rel_eq eq_OO values_def Rep_def o_apply
  by (tactic \<open>Local_Defs.unfold_tac @{context}
    (BNF_Def.bnf_of @{context} @{type_name G} |> the |> BNF_Def.set_defs_of_bnf)\<close>)
    (auto simp: rel_fun_def rel_set_eq elim: image_eqI[rotated])

lemma rel_lfset_eq_transfer[transfer_rule]:
  "rel_fun (=) (rel_fun (pcr_lfset (=) (=)) (rel_fun (pcr_lfset (=) (=)) (=))) (\<lambda>R. rel_fset (rel_prod (=) R)) (rel_lfset id)"
  unfolding rel_fun_def pcr_lfset_def cr_lfset_def prod.rel_eq fset.rel_eq eq_OO rel_lfset_def Rep_def o_apply
  by (tactic \<open>Local_Defs.unfold_tac @{context}
    [BNF_Def.bnf_of @{context} @{type_name G} |> the |> BNF_Def.rel_def_of_bnf]\<close>,
      simp add: Abs_G_inverse vimage2p_def eq_alt[symmetric])

end

lift_definition lfin :: "('a \<times> 'b) \<Rightarrow> ('a::large_G, 'b) lfset \<Rightarrow> bool" (infix "\<in>\<in>" 50) is fmember .

lemma lfin_map_lfset: "(a, b) \<in>\<in> map_lfset id g x \<longleftrightarrow> (\<exists>c. b = g c \<and> (a, c) \<in>\<in> x)"
  by transfer force

lemma lfin_label_inject: "(a, b) \<in>\<in> x \<Longrightarrow> (a, c) \<in>\<in> x \<Longrightarrow> b = c"
  by transfer (auto simp: nonrep_lfset_alt)

lift_definition lfempty :: "('a::large_G, 'b) lfset" is "{||} :: ('a \<times> 'b) fset"
  by (auto simp: nonrep_lfset_alt)

lemma labels_lfempty[simp]: "labels lfempty = {}"
  by transfer auto

lemma labels_empty_iff[simp]: "labels X = {} \<longleftrightarrow> X = lfempty"
  by transfer (auto simp: fmember.rep_eq)

lemma values_lfempty[simp]: "values lfempty = {}"
  by transfer auto

lemma lfin_lfempty[simp]: "x \<in>\<in> lfempty = False"
  by transfer auto

lemma lfin_values: "(l, c) \<in>\<in> x \<Longrightarrow> c \<in> values x"
  by transfer (force simp: fmember.rep_eq)

lemma finite_labels[simp]: "finite (labels x)"
  by transfer auto

lemma finite_values[simp]: "finite (values x)"
  by transfer auto

lemma values_lfin: "c \<in> values x \<Longrightarrow> \<exists>l. (l, c) \<in>\<in> x"
  by transfer (force simp: fmember.rep_eq)

lemma pred_lfset_lfempty[simp]: "pred_lfset P lfempty = True"
  unfolding lfset.pred_set by auto

lift_definition lfinsert :: "'a \<Rightarrow> 'b \<Rightarrow> ('a::large_G, 'b) lfset \<Rightarrow> ('a, 'b) lfset"
  is "\<lambda>a b X. if \<exists>c. b \<noteq> c \<and> (a, c) |\<in>| X then X else finsert (a, b) X"
  by (auto simp: nonrep_lfset_alt split_beta split: if_splits) metis

lift_definition lfupdate :: "('a::large_G, 'b) lfset \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) lfset"
  is "\<lambda>X a b. finsert (a, b) (ffilter (\<lambda>(a', _). a \<noteq> a') X)"
  by (auto simp: nonrep_lfset_alt)

lift_definition lfunion :: "('a::large_G, 'b) lfset \<Rightarrow> ('a, 'b) lfset \<Rightarrow> ('a, 'b) lfset"
  is "\<lambda>X Y. funion Y (ffilter (\<lambda>(a, _). a |\<notin>| fst |`| Y) X)"
  by (auto simp: nonrep_lfset_alt image_iff fBall.rep_eq fmember.rep_eq)

nonterminal lfupdbinds and lfupdbind

syntax
  "_lfupdbind" :: "'a \<Rightarrow> 'a \<Rightarrow> lfupdbind"                 ("(2_ :=/ _)")
  ""           :: "lfupdbind \<Rightarrow> lfupdbinds"               ("_")
  "_lfupdbinds":: "lfupdbind \<Rightarrow> lfupdbinds \<Rightarrow> lfupdbinds" ("_,/ _")
  "_lfUpdate"  :: "'a \<Rightarrow> lfupdbinds \<Rightarrow> 'a"                ("_/\<lbrace>(_)\<rbrace>" [1000, 0] 900)

translations
  "_lfUpdate f (_lfupdbinds b bs)" \<rightleftharpoons> "_lfUpdate (_lfUpdate f b) bs"
  "f\<lbrace>x:=y\<rbrace>" \<rightleftharpoons> "CONST lfupdate f x y"


subsection \<open>Size setup\<close>

lift_definition size_lfset :: "('a::large_G \<Rightarrow> nat) \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) lfset \<Rightarrow> nat" is
  "\<lambda>f g. size_fset (size_prod f g)" .

instantiation lfset :: (large_G,type) size begin
definition size_lfset where
  size_lfset_overloaded_def: "size_lfset = Labeled_FSet.size_lfset (\<lambda>_. 0) (\<lambda>_. 0)"
instance ..
end

lemmas size_lfset_simps =
  size_lfset_def[THEN meta_eq_to_obj_eq, THEN fun_cong, THEN fun_cong,
    unfolded map_fun_def comp_def id_apply]

lemmas size_lfset_overloaded_simps =
  size_lfset_simps[of "\<lambda>_. 0" "\<lambda>_. 0", unfolded add_0_left add_0_right,
    folded size_lfset_overloaded_def]

lemma lfset_size_o_map:
  "inj f \<Longrightarrow> size_lfset (\<lambda>_. 0) g \<circ> map_lfset_id f = size_lfset (\<lambda>_. 0) (g \<circ> f)"
  unfolding fun_eq_iff o_apply map_lfset_id_def
  by transfer
    (subst fun_cong[OF fset_size_o_map, unfolded o_apply],
    auto simp add: inj_on_def split_beta map_prod_def size_prod_simp)

setup \<open>
BNF_LFP_Size.register_size_global @{type_name lfset} @{const_name size_lfset}
  @{thm size_lfset_overloaded_def} @{thms size_lfset_simps size_lfset_overloaded_simps}
  @{thms lfset_size_o_map}
\<close>

lemma size_fset_estimation[termination_simp]: "x \<in> fset X \<Longrightarrow> y < f x \<Longrightarrow> y < size_fset f X"
  by (auto elim!: order.strict_trans2
    intro: order_trans[OF member_le_sum ordered_comm_monoid_add_class.sum_mono])

lemma size_fset_estimation'[termination_simp]: "x \<in> fset X \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> size_fset f X"
  by (auto elim!: order_trans
    intro: order_trans[OF member_le_sum ordered_comm_monoid_add_class.sum_mono])

lemma size_lfset_estimation[termination_simp]:
  "x \<in> values X \<Longrightarrow> y < f x \<Longrightarrow> y < size_lfset (\<lambda>_. 0) f X"
  by transfer (auto simp del: size_fset_simps intro!: size_fset_estimation)

lemma size_lfset_estimation'[termination_simp]:
  "x \<in> values X \<Longrightarrow> y \<le> f x \<Longrightarrow> y \<le> size_lfset (\<lambda>_. 0) f X"
  by transfer (auto simp del: size_fset_simps intro!: size_fset_estimation')

lift_definition apply_lfset :: "('a::large_G, 'b \<Rightarrow> 'c) lfset \<Rightarrow> ('a, 'b) lfset \<Rightarrow> ('a, 'c) lfset"
  is "\<lambda>F X. if fst |`| F |\<subseteq>| fst |`| X then (\<lambda>(a, f). (a, f (THE b. (a, b) |\<in>| X))) |`| F else {||}"
  by (force simp: nonrep_lfset_def)

lemma lfin_apply_lfset: "labels F \<subseteq> labels X \<Longrightarrow>
  (a, fx) \<in>\<in> apply_lfset F X \<longleftrightarrow> (\<exists>f x. fx = f x \<and> (a, f) \<in>\<in> F \<and> (a, x) \<in>\<in> X)"
  apply transfer
  apply (auto simp: fmember.rep_eq)
  subgoal for F X a f
    apply (drule set_mp[where x = a], force)
    apply safe
    subgoal for a' x
      apply (subst the1_equality[of _ x])
        apply (force simp: nonrep_lfset_def intro!: exI[of _ f] exI[of _ x])+
      done
    done
  subgoal for F X a f x
    apply (erule image_eqI[rotated])
    apply simp
    apply (subst the1_equality[of _ x])
      apply (force simp: nonrep_lfset_def)+
    done
  by force

lifting_update lfset.lifting
lifting_forget lfset.lifting
declare fun_cong[OF lfset_size_o_map, 
unfolded id_def inj_on_def, simplified, termination_simp]

hide_fact (open) FSet.bex_simps FSet.ball_simps


end