theory Make_Nonrep
  imports Common_Data_Codata_Bindings
begin

(* This theory shows that starting with the pullback-preserving MRBNF F, which is

a BNF in third and fourth position, small-support-endo-BNF in the first, and binder-BNF in the second

and applying Make_Binder at position 3 we obtain a pullback-preserving MRBNF F', which is

a BNF in fourth position, small-support-endo-BNF in the first, and binder-BNF in the second and third

*)

(* Assume strong BNF (on the BNF arguments only, here, 3 and 4 : *)
axiomatization where
  F_rel_map_set2_strong: 
  "\<And> R S (x :: ('a :: var_TT,'b :: var_TT,'c,'d) F) y.
    rrel_F R S x y =
      (\<exists>!z. set3_F z \<subseteq> {(x, y). R x y} \<and>
           set4_F z \<subseteq> {(x, y). S x y} \<and> map_F id id fst fst z = x \<and> map_F id id snd snd z = y)"
  and
(* The next property assumes that nonrepetitive elements exist: *)
  ex_nonrep: "\<exists>x. \<forall>x'. (\<exists> R. rrel_F R (=) x x') \<longrightarrow> (\<exists> f. x' = map_F id id f id x)"

lemma F_strong:
  "rel_F id id R3 R4 x y \<Longrightarrow> rel_F id id Q3 Q4 x y \<Longrightarrow> rel_F id id (inf R3 Q3) (inf R4 Q4) x y"
  unfolding rel_F_def F_map_id
  apply (frule F_rel_mono_strong0[OF supp_id_bound supp_id_bound bij_id supp_id_bound bij_id supp_id_bound,
    of _ _ _ _ top top, unfolded rel_F_def F_map_id]; auto?)
  apply (drule F_rel_map_set2_strong[THEN iffD1, of top])
  apply (unfold F_rel_map_set2_[OF supp_id_bound bij_id supp_id_bound, unfolded id_apply F_map_id OO_Grp_alt]
    id_def[symmetric])
  apply safe
  subgoal for z l r
    apply (frule spec2[of _ l z])
    apply (drule spec2[of _ r z])
    apply auto
    done
  done

(* The above is equivalent with preservation of (strong) pullbacks; it is preserved by 
composition and (co)data, giving the "free/nonpermutative" (co)datatypes. 
It is satisfied by the basic BNFs, but not by set-like BNFs.  *)

(* It implies the following "exchange"-property, which could be read: 
Since the atoms have a fixed position, we can permute the relations: *)
lemma rel_F_exchange: 
  fixes x :: "('a1::var_TT,'a2::var_TT,'a3,'a4) F" and x' :: "('a1,'a2,'a3','a4') F"
  assumes "rel_F id id R2 R3 x x'" and "rel_F id id Q2 Q3 x x'"
  shows "rel_F id id R2 Q3 x x'" 
  by (rule F_rel_mono_strong1[OF supp_id_bound bij_id supp_id_bound F_strong[OF assms]]) auto

definition sameShape1 :: "('a1::var_TT,'a2::var_TT,'a3,'a4) F \<Rightarrow> ('a1,'a2,'a3,'a4) F \<Rightarrow> bool" where 
  "sameShape1 x x' \<equiv> \<exists> R. rel_F id id R (=) x x'"

definition nonrep2 :: "('a1::var_TT,'a2::var_TT,'a3,'a4) F \<Rightarrow> bool" where 
  "nonrep2 x \<equiv> \<forall> x'. sameShape1 x x' \<longrightarrow> (\<exists> f. x' = map_F id id f id x)"

lemma op_eq_triv_sym: "(\<lambda>x. (=) (g x)) = (\<lambda>x z. z = g x)"
  by force

lemma nonrep2_map_F:
  fixes x :: "('a1::var_TT,'a2::var_TT,'a3,'a4) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'b4"
  assumes v: "|supp v| <o bound(any::'a1)"  and u: "bij u" "|supp u| <o bound(any::'a2)" 
  assumes "nonrep2 x"
  shows "nonrep2 (map_F v u id g x)"
unfolding nonrep2_def sameShape1_def proof safe
  fix y' :: "('a1,'a2,'a3,'b4) F" and R
  let ?y = "map_F v u id g x"
  assume r: "rel_F id id R (=) ?y y'"
  have "rel_F (v o id) (u o id) (R OO (=)) (Grp id OO Grp g) x y'"
    using r unfolding F_rel_map_left[OF supp_id_bound v bij_id supp_id_bound u] 
    by (simp add: OO_def Grp_def op_eq_triv_sym[of g]) 
  then obtain x' where xx': "rel_F id id R (=) x x'" and y': "y' = map_F v u id g x'" 
    unfolding F_rel_comp[OF supp_id_bound v bij_id supp_id_bound u]
    unfolding OO_def eq_alt
      F_rel_Grp[OF v u] unfolding Grp_def by auto
  obtain f where x': "x' = map_F id id f id x" 
    using assms xx' unfolding nonrep2_def sameShape1_def by auto
  show "\<exists>f. y' = map_F id id f id ?y"
    apply(rule exI[of _ f]) unfolding y' x'  
      F_map_comp[symmetric, OF v supp_id_bound u bij_id supp_id_bound]
      F_map_comp[symmetric, OF supp_id_bound v bij_id supp_id_bound u]
    by simp
qed

(* Here we use the BNF strength: *)
lemma nonrep2_map_F_rev:
  fixes x :: "('a1::var_TT,'a2::var_TT,'a3,'a4) F" and u :: "'a2\<Rightarrow>'a2" and g :: "'a4 \<Rightarrow> 'b4"
  assumes u: "bij u" "|supp u| <o bound(any::'a2)" 
  assumes "nonrep2 (map_F id u id g x)"
  shows "nonrep2 x"
  unfolding nonrep2_def sameShape1_def proof safe
  fix x' :: "('a1,'a2,'a3,'a4) F" and R 
  let ?y = "map_F id u id g x"  let ?y' = "map_F id u id g x'"
  assume r: "rel_F id id R (=) x x'"
  hence "rel_F id id R (=) ?y ?y'" 
    unfolding F_rel_map_left[OF supp_id_bound supp_id_bound bij_id supp_id_bound u]  
    using F_rel_map_right[OF supp_id_bound supp_id_bound u bij_id supp_id_bound, of R "(=)" x x' id g]  
    by (simp add: op_eq_triv_sym[of g] OO_def Grp_def)
  then obtain f where "?y' = map_F id id f id ?y" 
    using assms unfolding nonrep2_def sameShape1_def by auto
  hence y':"?y' = map_F id u f g x"
    unfolding F_map_comp[symmetric, OF supp_id_bound supp_id_bound bij_id supp_id_bound u] by simp
  hence "rel_F id u (Grp id) (Grp g) x' (map_F id u f g x)"
    unfolding F_rel_Grp[OF supp_id_bound u, of id g] by (simp add: Grp_def)
  hence "rel_F id id (Grp f) (Grp g OO conversep (Grp g)) x x'"
    apply(subst F_rel_flip[OF bij_id supp_id_bound bij_id supp_id_bound, simplified, symmetric])
    unfolding F_rel_map_right_bij[OF supp_id_bound bij_id supp_id_bound u u] Grp_def
    by (simp add: u conversep_def OO_def F.rel_mono_strong0)
  from rel_F_exchange[OF this r]
  have "rel_F id id (Grp f) (=) x x'" .
  thus "\<exists>f. x' = map_F id id f id x" 
    apply(intro exI[of _ f])  unfolding eq_alt F.rel_Grp by (simp add: Grp_def)
qed

lemma nonrep2_mapF_bij:
  fixes x :: "('a1::var_TT,'a2::var_TT,'a3,'a4) F" and g::"'a3\<Rightarrow>'a3"
  assumes g: "bij g" and x: "nonrep2 x"
  shows "nonrep2 (map_F id id g id x)" (is "nonrep2 ?x'")
  unfolding nonrep2_def sameShape1_def proof safe
  fix y' :: "('a1,'a2,'a3,'a4)F" and R'
  let ?y = "map_F id id (inv g) id y'" 
  let ?R = "Grp g OO R' OO conversep (Grp g)"
  assume "rel_F id id R' (=) ?x' y'"
  hence "rel_F id id ?R (=) x ?y"
    unfolding F_rel_map_left[OF supp_id_bound supp_id_bound bij_id supp_id_bound bij_id supp_id_bound]
      F_rel_map_right_bij[OF supp_id_bound bij_id supp_id_bound bij_id supp_id_bound bij_id supp_id_bound] 
    by (simp add: g Grp_def OO_def o_def id_def)
  with x obtain f where "?y = map_F id id f id x" 
    unfolding nonrep2_def sameShape1_def by auto
  thus "\<exists>f'. y' = map_F id id f' id ?x'"
    apply(intro exI[of _ "g o f o inv g"])
    apply(simp add: g F.map_comp o_assoc[symmetric]) 
    by (metis F.map_comp F.map_id comp_id g inv_o_simp2)  
qed

lemma nonrep2_mapF_bij_2:
  fixes x :: "('a1::var_TT,'a2::var_TT,'a3,'a4) F"
    and v :: "'a1 \<Rightarrow> 'a1" and u :: "'a2\<Rightarrow>'a2" and g::"'a3\<Rightarrow>'a3" and f::"'a4\<Rightarrow>'a4'"
  assumes v: "|supp v| <o bound(any::'a1)" and u: "bij u" "|supp u| <o bound(any::'a2)"
    and g: "bij g" and x: "nonrep2 x"
  shows "nonrep2 (map_F v u g f x)" 
proof-
  have "nonrep2 (map_F v u id f x)" (is "nonrep2 ?x'") by (simp add: nonrep2_map_F v u x)
  hence "nonrep2 (map_F id id g id ?x')" using g nonrep2_mapF_bij u by blast
  thus ?thesis unfolding F_map_comp[OF supp_id_bound v bij_id supp_id_bound u, symmetric]
    by simp
qed

typedef ('a1::var_TT,'a2::var_TT,'a3::var_TT,'a4) F' = "{x :: ('a1,'a2,'a3,'a4) F. nonrep2 x}"
  unfolding mem_Collect_eq nonrep2_def sameShape1_def rel_F_def F_map_id id_apply
  unfolding id_def[symmetric]
  by (rule ex_nonrep)

setup_lifting type_definition_F'

lift_definition set1_F' :: "('a1::var_TT,'a2::var_TT,'a3::var_TT,'a4) F' \<Rightarrow> 'a1 set" is set1_F .
lift_definition set2_F' :: "('a1::var_TT,'a2::var_TT,'a3::var_TT,'a4) F' \<Rightarrow> 'a2 set" is set2_F .
lift_definition set3_F' :: "('a1::var_TT,'a2::var_TT,'a3::var_TT,'a4) F' \<Rightarrow> 'a3 set" is set3_F .
lift_definition set4_F' :: "('a1::var_TT,'a2::var_TT,'a3::var_TT,'a4) F' \<Rightarrow> 'a4 set" is set4_F .

lift_definition map_F' :: "('a1::var_TT \<Rightarrow> 'a1) \<Rightarrow> ('a2::var_TT \<Rightarrow> 'a2) \<Rightarrow> ('a3::var_TT \<Rightarrow> 'a3) \<Rightarrow> ('a4 \<Rightarrow> 'a4') 
  \<Rightarrow> ('a1,'a2,'a3,'a4) F' \<Rightarrow> ('a1,'a2,'a3,'a4') F'"
  is "\<lambda>v u f g. map_F (asSS v) (asSS (asBij u)) (asBij f) g" 
  unfolding asBij_def asSS_def by (auto simp: supp_id_bound intro: nonrep2_mapF_bij_2)

lift_definition rrel_F' :: "('a4 \<Rightarrow> 'a4' \<Rightarrow> bool) \<Rightarrow> ('a1::var_TT,'a2::var_TT,'a3::var_TT,'a4) F' \<Rightarrow> ('a1,'a2,'a3,'a4') F' \<Rightarrow> bool"
  is "rrel_F (=)" .

(* Verifying the axioms of a MRBNF *)

lemma F'_map_id: "map_F' id id id id = id"
  by (rule ext, transfer) (auto simp: F_map_id asSS_def)

lemma F'_map_comp1_:
  fixes u1 v1 :: "'a1::var_TT \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var_TT \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var_TT \<Rightarrow> 'a3"
  assumes "|supp u1| <o bound(any::'a1)" "|supp v1| <o bound(any::'a1)"
  assumes "bij u2" "|supp u2| <o bound(any::'a2)" "bij v2" "|supp v2| <o bound(any::'a2)"
  assumes "bij u3" "|supp u3| <o bound(any::'a3)" "bij v3" "|supp v3| <o bound(any::'a3)"
  shows "map_F' (v1 o u1) (v2 o u2) (v3 o u3) (g o f) = map_F' v1 v2 v3 g o map_F' u1 u2 u3 f"
  using assms by (intro ext, transfer)
    (auto simp: F_map_comp assms asBij_def asSS_def supp_comp_bound supp_id_bound)

lemma F'_set1_map_:
  fixes u1 :: "'a1::var_TT \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var_TT \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var_TT \<Rightarrow> 'a3"
  assumes "|supp u1| <o bound(any::'a1)"
  assumes "bij u2" "|supp u2| <o bound(any::'a2)"
  assumes "bij u3" "|supp u3| <o bound(any::'a3)"
  shows "set1_F' (map_F' u1 u2 u3 f b) = u1 ` set1_F' b"
  using assms by transfer (auto simp: F_set_map asSS_def)

lemma F'_set2_map_:
  fixes u1 :: "'a1::var_TT \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var_TT \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var_TT \<Rightarrow> 'a3"
  assumes "|supp u1| <o bound(any::'a1)"
  assumes "bij u2" "|supp u2| <o bound(any::'a2)"
  assumes "bij u3" "|supp u3| <o bound(any::'a3)"
  shows "set2_F' (map_F' u1 u2 u3 f b) = u2 ` set2_F' b"
  using assms by transfer (auto simp: F_set_map asSS_def)

lemma F'_set3_map_:
  fixes u1 :: "'a1::var_TT \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var_TT \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var_TT \<Rightarrow> 'a3"
  assumes "|supp u1| <o bound(any::'a1)"
  assumes "bij u2" "|supp u2| <o bound(any::'a2)"
  assumes "bij u3" "|supp u3| <o bound(any::'a3)"
  shows "set3_F' (map_F' u1 u2 u3 f b) = u3 ` set3_F' b"
  using assms by transfer (auto simp: F_set_map asSS_def)

lemma F'_set4_map_:
  fixes u1 :: "'a1::var_TT \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var_TT \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var_TT \<Rightarrow> 'a3"
  assumes "|supp u1| <o bound(any::'a1)"
  assumes "bij u2" "|supp u2| <o bound(any::'a2)"
  assumes "bij u3" "|supp u3| <o bound(any::'a3)"
  shows "set4_F' (map_F' u1 u2 u3 f b) = f ` set4_F' b"
  using assms by transfer (auto simp: F_set_map asSS_def)

lemma F'_map_cong_[fundef_cong]:
  fixes u1 v1 :: "'a1::var_TT \<Rightarrow> 'a1"
  fixes u2 v2 :: "'a2::var_TT \<Rightarrow> 'a2"
  fixes u3 v3 :: "'a3::var_TT \<Rightarrow> 'a3"
  assumes "|supp u1| <o bound(any::'a1)" "|supp v1| <o bound(any::'a1)"
  assumes "bij u2" "|supp u2| <o bound(any::'a2)" "bij v2" "|supp v2| <o bound(any::'a2)"
  assumes "bij u3" "|supp u3| <o bound(any::'a3)" "bij v3" "|supp v3| <o bound(any::'a3)"
    and "\<forall> a \<in> set1_F' x. u1 a = v1 a"
    and "\<forall> a \<in> set2_F' x. u2 a = v2 a"
    and "\<forall> a \<in> set3_F' x. u3 a = v3 a"
    and "\<forall> a \<in> set4_F' x. f a = g a"
  shows "map_F' u1 u2 u3 f x = map_F' v1 v2 v3 g x"
  using assms by transfer (auto intro: F_map_cong simp: asSS_def)

lemma F'_set1_bd: "\<And>b. |set1_F' b| <o bd_TT"
  by transfer (simp add: F_set1_bd)
lemma F'_set2_bd: "\<And>b. |set2_F' b| <o bd_TT"
  by transfer (simp add: F_set2_bd)
lemma F'_set3_bd: "\<And>b. |set3_F' b| <o bd_TT"
  by transfer (simp add: F_set3_bd)

lemma F'_rel_comp_leq_: "rrel_F' Q OO rrel_F' R \<le> rrel_F' (Q OO R)"
  by (intro predicate2I, transfer)
    (auto intro: F_rel_comp_leq_[of "(=)" _ "(=)", simplified, THEN predicate2D])

(*
lemma F'_rel_map_set_bij: 
  fixes u :: "'a1::var_F \<Rightarrow> 'a1" and R3 :: "'a3 \<Rightarrow> 'a3' \<Rightarrow> bool"
  assumes u: "bij u" "|supp u| <o bound(any::'a1)"  
  assumes "bij (u2::'a2\<Rightarrow>'a2)" and nx: "nonrep2 x" and ny: "nonrep2 y"
  shows 
    "rel_F u (Grp u2) R3 x y \<longleftrightarrow>
 (\<exists>z. nonrep2 z \<and>
      set3_F z \<subseteq> {(x, y). R3 x y} \<and> map_F id id fst z = x \<and> map_F u u2 snd z = y)"
    (is "?A \<longleftrightarrow> ?B")
proof 
  assume ?A
  then obtain z :: "('a1, 'a2 \<times> 'a2, 'a3 \<times> 'a3') F" 
    where 2: "set2_F z \<subseteq> {(x, y). Grp u2 x y}"
      and 3: "set3_F z \<subseteq> {(x, y). R3 x y}"
      and x: "x = map_F id fst fst z" and y: "y = map_F u snd snd z" 
    unfolding F_rel_map_set[OF u] by auto
  show ?B apply(rule exI[of _ "map_F id fst id z"], safe)
    subgoal using nx by (simp add: x nonrep2_map_F_rev[OF id] F_map_comp[OF id id, symmetric])
    subgoal using 3 unfolding F_set_map[OF id] by auto
    subgoal using x by (simp add: F_map_comp[OF id id, symmetric])
    subgoal unfolding y using 2 by (auto simp add: F_map_comp[OF id u, symmetric] Grp_def intro!: F_map_cong[OF u u])
    done
next 
  assume ?B
  then obtain z where z: "nonrep2 z" and 3: "set3_F z \<subseteq> {(x, y). R3 x y}"
    and x: "map_F id id fst z = x" and y: "map_F u u2 snd z = y" by auto
  show ?A unfolding F_rel_map_set[OF u]
    apply(rule exI[of _ "map_F id (\<lambda>x. (x, u2 x)) id z"], safe)
    subgoal by (simp add: F_set2_map[OF id] Grp_def image_def)
    subgoal using 3 by (auto simp: F_set3_map[OF id] Grp_def image_def)
    subgoal by(simp add: F_map_comp[OF id id, symmetric] o_def x id_def[symmetric])
    subgoal by(simp add: F_map_comp[OF id u, symmetric] o_def y)
    done
qed

lemma F'_rel_map_set2:
  fixes u :: "'a1::var_F \<Rightarrow> 'a1" 
  assumes u: "bij u" "|supp u| <o bound(any::'a1)"  
  assumes "bij (u2::'a2\<Rightarrow>'a2)"  
  shows 
    "rel_F' u u2 R3 x y \<longleftrightarrow>  
 (\<exists>z. set3_F' z \<subseteq> {(x, y). R3 x y} \<and> 
      map_F' id id fst z = x \<and> map_F' u u2 snd z = y)" 
  using assms by (transfer) (simp add: u F'_rel_map_set_bij)
*)

lemma rrel_F_bij:
  fixes x :: "('a :: var_TT,'b :: var_TT,'c,'d) F"
  assumes "bij f"
  shows "rrel_F (Grp (f :: 'c \<Rightarrow> 'c)) R x y = rrel_F (=) R (map_F id id f id x) y"
  unfolding F_rel_map_set2_[OF supp_id_bound bij_id supp_id_bound, unfolded F_map_id id_apply]
  apply safe
  subgoal for z
    by (force simp: id_def[symmetric] F_map_comp[symmetric] supp_id_bound Grp_def F_set_map
      intro!: F.map_cong exI[of _ "map_F id id (\<lambda>x. (snd x, snd x)) id z"])
  subgoal for z
    apply (drule arg_cong[of _ _ "map_F id id (inv f) id"])
    apply (auto simp: id_def[symmetric] F_map_comp[symmetric] supp_id_bound Grp_def F_set_map
      assms o_def F_map_id)
    apply (rule exI[of _ "map_F id id (\<lambda>(_, x). (inv f x, x)) id z"])
    apply (auto simp: F_set_map supp_id_bound assms F_map_comp[symmetric]
      intro!:  F.map_cong)
    done
  done

lemma F'_rel_map_set2_:
  fixes u1 :: "'a1::var_TT \<Rightarrow> 'a1"
  fixes u2 :: "'a2::var_TT \<Rightarrow> 'a2"
  fixes u3 :: "'a3::var_TT \<Rightarrow> 'a3"
  assumes u1: "|supp u1| <o bound(any::'a1)"
    and u2: "bij u2" "|supp u2| <o bound(any::'a2)" 
    and u3: "bij u3" "|supp u3| <o bound(any::'a3)"
  shows "rrel_F' R (map_F' u1 u2 u3 id x) y =
    (\<exists>z. set4_F' z \<subseteq> {(x, y). R x y} \<and> map_F' id id id fst z = x \<and> map_F' u1 u2 u3 snd z = y)"
  using assms
  apply (transfer fixing: u1 u2 u3 R)
  apply (auto simp: asSS_def asBij_def
    trans[OF rrel_F_bij[OF u3(1), symmetric] F_rel_map_set2_[OF u1 u2],
      unfolded F_map_comp[OF supp_id_bound u1 bij_id supp_id_bound u2, symmetric] id_o o_id])
  subgoal for z
    apply (rule exI[of _ "map_F id id fst id z"])
    apply (auto simp: F_set_map supp_id_bound F_map_comp[symmetric] Grp_def
      intro!: F_map_cong nonrep2_map_F_rev[OF bij_id supp_id_bound, of fst])
    done
  subgoal for z
    apply (rule exI[of _ "map_F id id (\<lambda>x. (x, u3 x)) id z"])
    apply (auto simp: F_set_map supp_id_bound F_map_comp[symmetric] Grp_def
      intro!: F_map_cong)
    done
  done

lemma F'_strong:
  assumes "rrel_F' R x x'" 
    and "rrel_F' Q x x'"
  shows "rrel_F' (inf R Q) x x'" 
  using assms apply transfer using F_strong unfolding rel_F_def F_map_id by fastforce

thm \<comment> \<open>MRBNF properties\<close>
  F'_map_id
  F'_map_comp1_
  F'_set1_map_ 
  F'_set2_map_
  F'_set3_map_
  F'_map_cong_
  F'_set1_bd
  F'_set2_bd
  F'_set3_bd
  F.bd_card_order
  F.bd_cinfinite
  F'_rel_comp_leq_
  F'_rel_map_set2_


end