theory Common_Data_Codata_Bindings
  imports "../Prelim"  "Labeled_FSet"
begin
  
abbreviation "bound(a::'a) \<equiv> |UNIV :: 'a set|"
  
(* The following are replaced by the concrete items defining 
the desired syntax: *)
(* typedecl ('a,'b,'c,'d) F   
consts map_F :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'c') \<Rightarrow> ('d \<Rightarrow> 'd') \<Rightarrow> ('a,'b,'c,'d) F \<Rightarrow> ('a,'b,'c','d')F"
consts set1_F :: "('a,'b,'c,'d) F \<Rightarrow> 'a set"
consts set2_F :: "('a,'b,'c,'d) F \<Rightarrow> 'b set"
consts set3_F :: "('a,'b,'c,'d) F \<Rightarrow> 'c set"
consts set4_F :: "('a,'b,'c,'d) F \<Rightarrow> 'd set"
consts rrel_F :: "('c \<Rightarrow> 'c' \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c,'d) F \<Rightarrow> ('a,'b,'c','d')F \<Rightarrow> bool"
consts wit_F :: "('a,'b,'c','d) F"

typedecl bd_type_TT
consts bd_TT :: "bd_type_TT rel"
*)

(****)
(* Types of System F with nested records 
(an extension of the types in the paper's Example 13): *)
type_synonym label = nat (*large enough*)
datatype (set1_F: 'ctvarf, set2_F: 'ctvarb, set3_F: 'ctypef, set4_F: 'ctypeb) LIVE_F =
  FVar 'ctvarf | FTop | FArr 'ctypef 'ctypef | FAll 'ctvarb 'ctypef 'ctypeb | 
  FRec "(label, 'ctypef) lfset"
for map: map_F
definition "wit_F \<equiv> FVar any" 
type_synonym bd_type_TT = "nat"
definition bd_TT::"nat rel" 
where "bd_TT = natLeq"

(* AFTER THIS, GENERIC DEVELOPMENT 
(the same for any syntax matching the given MRBNF arity): *)

type_synonym ('a,'b,'c,'d) F = "('a,'b,'c,'d) LIVE_F"
definition "rrel_F \<equiv> rel_LIVE_F (=) (=)"  
 
class var_TT = assumes var_TT: "bd_TT \<le>o bound(any::'a) \<and> 
                                regularCard (bound(any::'a))"

(* Possible instantiation: *)
instantiation nat :: var_TT begin
instance 
apply standard apply (simp add: natLeq_Card_order 
stable_nat stable_regularCard bd_TT_def)
done
end

lemma F_set_finite:
  "finite (set1_F x)"
  "finite (set2_F x)"
  "finite (set3_F x)"
  "finite (set4_F x)"
  by (cases x; auto)+

(* Verifying the MRBNF assumptions: *)  
lemma 
    F_map_id: "map_F id id id id = id"
and F_map_comp1:
"\<And> (u::'a::var_TT\<Rightarrow>'a) u' (v::'b::var_TT\<Rightarrow>'b) v' f f' g g'.
    |supp u| <o bound(any::'a) \<Longrightarrow> |supp u'| <o bound(any::'a) \<Longrightarrow>
    bij v \<Longrightarrow> |supp v| <o bound(any::'b) \<Longrightarrow> bij v' \<Longrightarrow> |supp v'| <o bound(any::'b) \<Longrightarrow>
    map_F (u o u') (v o v') (f o f') (g o g') = map_F u v f g o map_F u' v' f' g'"
and F_set1_map:
"\<And> (u::'a::var_TT\<Rightarrow>'a) (v::'b::var_TT\<Rightarrow>'b) f g b.
    |supp u| <o bound(any::'a) \<Longrightarrow>
    bij v \<Longrightarrow> |supp v| <o bound(any::'b) \<Longrightarrow> set1_F (map_F u v f g b) = u ` set1_F b"
and F_set2_map:
"\<And> (u::'a::var_TT\<Rightarrow>'a) (v::'b::var_TT\<Rightarrow>'b) f g b.
    |supp u| <o bound(any::'a) \<Longrightarrow>
    bij v \<Longrightarrow> |supp v| <o bound(any::'b) \<Longrightarrow> set2_F (map_F u v f g b) = v ` set2_F b"
and F_set3_map:
"\<And> (u::'a::var_TT\<Rightarrow>'a) (v::'b::var_TT\<Rightarrow>'b) f g b.
    |supp u| <o bound(any::'a) \<Longrightarrow>
    bij v \<Longrightarrow> |supp v| <o bound(any::'b) \<Longrightarrow> set3_F (map_F u v f g b) = f ` set3_F b"
and F_set4_map:
"\<And> (u::'a::var_TT\<Rightarrow>'a) (v::'b::var_TT\<Rightarrow>'b) f g b.
    |supp u| <o bound(any::'a) \<Longrightarrow>
    bij v \<Longrightarrow> |supp v| <o bound(any::'b) \<Longrightarrow> set4_F (map_F u v f g b) = g ` set4_F b"
and F_map_cong[fundef_cong]:
"\<And> (u::'a::var_TT\<Rightarrow>'a) u' (v::'b::var_TT\<Rightarrow>'b) v' f f' g g' x.
    |supp u| <o bound(any::'a) \<Longrightarrow> |supp u'| <o bound(any::'a) \<Longrightarrow>
    bij v \<Longrightarrow> |supp v| <o bound(any::'b) \<Longrightarrow> bij v' \<Longrightarrow> |supp v'| <o bound(any::'b) \<Longrightarrow>
    \<forall> a \<in> set1_F x. u a = u' a \<Longrightarrow>
    \<forall> b \<in> set2_F x. v b = v' b \<Longrightarrow>
    \<forall> c \<in> set3_F x. f c = f' c \<Longrightarrow>
    \<forall> d \<in> set4_F x. g d = g' d \<Longrightarrow>
    map_F u v f g x = map_F u' v' f' g' x"
and bd_TT_card_order: "card_order bd_TT"
and F_set1_bd: "\<And>b. |set1_F b| <o bd_TT"
and F_set2_bd: "\<And>b. |set2_F b| <o bd_TT"
and F_set3_bd: "\<And>b. |set3_F b| <o bd_TT"
and F_set4_bd: "\<And>b. |set4_F b| <o bd_TT"
and bd_TT_cinfinite: "cinfinite bd_TT"
and F_rel_comp_leq_:  
"\<And> R R' S S'. rrel_F R S OO rrel_F R' S' \<le> rrel_F (R OO R') (S OO S')"
and F_rel_map_set2_: 
"\<And> (u::'a::var_TT\<Rightarrow>'a) (v::'b::var_TT\<Rightarrow>'b) R S x y. 
  |supp u| <o bound(any::'a) \<Longrightarrow> bij v \<Longrightarrow> |supp v| <o bound(any::'b) \<Longrightarrow>  
  rrel_F R S (map_F u v id id x) y =
    (\<exists>z. set3_F z \<subseteq> {(x, y). R x y} \<and>
         set4_F z \<subseteq> {(x, y). S x y} \<and> map_F id id fst fst z = x \<and> map_F u v snd snd z = y)"
and F_wit1: "set3_F wit_F = {}"
and F_wit2: "set4_F wit_F = {}"
apply(rule LIVE_F.map_id0)
apply(rule LIVE_F.map_comp0) 
apply (rule LIVE_F.set_map(1)) 
apply (rule LIVE_F.set_map(2)) 
apply (rule LIVE_F.set_map(3)) 
apply (rule LIVE_F.set_map(4)) 
apply(rule LIVE_F.map_cong, simp_all)
apply (simp add: bd_TT_def F_set_finite finite_iff_ordLess_natLeq[symmetric]
  cardSuc_ordLeq_ordLess LIVE_F.set_bd LIVE_F.bd_card_order natLeq_card_order
  natLeq_cinfinite)+ 
unfolding rrel_F_def  
apply(rule preorder_class.eq_refl[OF 
LIVE_F.rel_compp[symmetric], of "(=)" "(=)" _ _ "(=)" "(=)", simplified])
subgoal for u v R S x y  
unfolding LIVE_F.rel_map(1)
unfolding LIVE_F.in_rel apply safe
  subgoal for z
  apply(rule exI[of _ "map_F fst fst id id z"]) 
  apply (auto simp: LIVE_F.set_map LIVE_F.map_comp intro!: LIVE_F.map_cong) .
  subgoal for z   
  apply(rule exI[of _ "map_F (\<lambda>a. (a,u a)) (\<lambda>a. (a,v a)) id id z"])  
  apply (auto simp: LIVE_F.set_map LIVE_F.map_comp intro!: LIVE_F.map_cong) . .
  unfolding wit_F_def by auto 

lemma bd_TT_Card_order: "Card_order bd_TT"
  using bd_TT_card_order card_order_on_Card_order by auto
    
lemma (in var_TT) UNIV_cinfinite: "cinfinite (bound(any::'a))"
  using bd_TT_cinfinite cinfinite_mono var_TT by blast

(* CARDINAL SETUP FOR THE TO-BE-DEFINED TYPE TT OF (QUOTIENTED) TERMS *)

(* For datatypes, we care about backwards compatibility with the finitary case: *)

(* For codatatypes, we need a larger bound: *)
definition bbd_TT where "bbd_TT \<equiv> cardSuc bd_TT"

class vvar_TT = assumes vvar_TT: "bbd_TT \<le>o bound(any::'a) \<and> regularCard (bound(any::'a))"

(* Everything we prove for a type of class var_TT will automnatically be inheritted 
to vvar_TT: *)
subclass (in vvar_TT) var_TT
  apply standard
  by (metis bbd_TT_def bd_TT_card_order cardSuc_ordLess_ordLeq card_of_card_order_on
    card_order_on_Card_order vvar_TT ordLess_imp_ordLeq)

(* In addition, we have the property which var_TT avoided for backwards compatibility, 
but is crucial for codatatypes: *)
lemma natLeq_bound: "natLeq <o bound(any::'a::vvar_TT)"
proof-
  have "natLeq \<le>o bd_TT"
    by (metis natLeq_ordLeq_cinfinite bd_TT_cinfinite bd_TT_Card_order)
  hence "natLeq <o bbd_TT" unfolding bbd_TT_def
    by (simp add: bd_TT_Card_order natLeq_Card_order)
  also have"bbd_TT \<le>o |UNIV::'a set|" by (simp add: vvar_TT) 
  finally show ?thesis .
qed 
(*    *)

lemmas bound_Card_order = card_of_Card_order[of "UNIV::('a::var_TT)set"]    
    
lemmas bound_card_order = card_of_card_order_on[of "UNIV::('a::var_TT)set"]
 
lemma bound_regularCard: "regularCard (bound(any::'a::var_TT))"
  by (simp add: var_TT) 
    
lemmas bound_cinfinite = var_TT_class.UNIV_cinfinite
  
typedef wit_vvar_TT = "Field bbd_TT"
  unfolding bbd_TT_def
  by (simp add: Field_cardSuc_not_empty bd_TT_Card_order ex_in_conv)

lemma wit_var_TT_ordIso_bd_TT_type_set: "bbd_TT =o |UNIV:: wit_vvar_TT set|" 
proof-
  have "|UNIV:: wit_vvar_TT set| =o |Field bbd_TT|" 
  using Abs_wit_vvar_TT_inverse  
  by (intro card_of_ordIsoI[of Rep_wit_vvar_TT])  (auto simp: Rep_wit_vvar_TT_inject 
       Rep_wit_vvar_TT bij_betw_def inj_on_def)  
  thus ?thesis
    unfolding bbd_TT_def
    using Card_order_iff_ordIso_card_of bd_TT_Card_order cardSuc_Card_order ordIso_symmetric ordIso_transitive
    by blast
qed
  
lemma bbd_TT_ordLeq_wit_vvar_TT: 
  "bbd_TT \<le>o |UNIV:: wit_vvar_TT set|" 
  using ordIso_iff_ordLeq wit_var_TT_ordIso_bd_TT_type_set by blast

lemma regularCard_wit_vvar_TT: "regularCard |UNIV:: wit_vvar_TT set|"
  by (metis Cinfinite_cardSuc Cnotzero_UNIV bbd_TT_def bbd_TT_ordLeq_wit_vvar_TT bd_TT_Card_order
    bd_TT_cinfinite cinfinite_def cinfinite_mono infinite_cardSuc_regularCard regularCard_ordIso
    wit_var_TT_ordIso_bd_TT_type_set)
 
(*  Need to instantiate the class, else datatype construction will fail: *)
instantiation wit_vvar_TT :: vvar_TT
begin
instance by standard (auto simp : regularCard_wit_vvar_TT bbd_TT_ordLeq_wit_vvar_TT)
end

lemma var_TT_infinite:
  "infinite (UNIV :: ('a :: var_TT) set)"
  using bound_cinfinite Cnotzero_UNIV cardSuc_finite card_of_cardSuc_finite
  unfolding cinfinite_def by auto

lemma emp_bound: "|{}| <o bound(any::'a::var_TT)"
  by (simp add: card_of_empty4)

lemma set1_F_bound: "|set1_F x| <o bound(any::'a::var_TT)"
  using F_set1_bd ordLess_ordLeq_trans var_TT by blast

lemma set2_F_bound: "|set2_F x| <o bound(any::'a::var_TT)"
  using F_set2_bd ordLess_ordLeq_trans var_TT by blast

lemma set3_F_bound: "|set3_F x| <o bound(any::'a::var_TT)"
  using F_set3_bd ordLess_ordLeq_trans var_TT by blast

lemma set4_F_bound: "|set4_F x| <o bound(any::'a::var_TT)"
  using F_set4_bd ordLess_ordLeq_trans var_TT by blast

lemma singl_bound: "|{a}| <o bound(any::'a::var_TT)"
  using finite_ordLess_infinite var_TT_class.UNIV_cinfinite[unfolded cinfinite_def] by force 

lemma Un_bound:
  assumes "|A1| <o bound(any::'a::var_TT)" and "|A2| <o bound(any::'a)"
  shows "|A1 \<union> A2| <o bound(any::'a)"
  using assms card_of_Un_ordLess_infinite var_TT_class.UNIV_cinfinite[unfolded cinfinite_def] by auto

lemma UNION_bound:
  assumes "|I| <o bound(any::'a::var_TT)" and "\<And>i. i \<in> I \<Longrightarrow> |A i| <o bound(any::'a)"
  shows "|\<Union>i\<in>I. A i| <o bound(any::'a)"
  by (simp add: assms bound_Card_order bound_cinfinite bound_regularCard regularCard_UNION)

lemma imsupp_supp_bound:
  "|imsupp g| <o bound(any::'a::var_TT) \<longleftrightarrow> |supp g| <o bound(any::'a)"
  by (metis Un_bound card_of_image imsupp_def ordLeq_ordLess_trans supp_ordleq_imsupp)

lemma supp_id_bound: "|supp id| <o bound(any::'a::var_TT)"
  by (simp add: emp_bound supp_id)

lemma supp_id_upd: "|supp (id(a := a'))| <o bound(any::'a::var_TT)"
  unfolding supp_def by (cases "a = a'") (auto simp: singl_bound emp_bound)

lemma supp_inv_bound:
  assumes b: "bij f" and s: "|supp f| <o bound(any::'a::var_TT)"
  shows "|supp (inv f)| <o bound(any::'a)"
  unfolding supp_inv[OF b]
  using s card_of_image ordLeq_ordLess_trans by blast

lemma supp_comp_bound:
  assumes "|supp g| <o bound(any::'a::var_TT)" and "|supp f| <o bound(any::'a)"
  shows "|supp (g o f)| <o bound(any::'a)"
  by (meson Un_bound assms card_of_mono1 ordLeq_ordLess_trans supp_o)

lemma supp_imsupp_bound: "|supp f| <o bound(any::'a::var_TT) \<Longrightarrow> |imsupp f| <o bound(any::'a)"
  unfolding imsupp_supp_bound by auto
 
lemma F_map_comp:
  fixes u u'::"'a::var_TT\<Rightarrow>'a" and v v' :: "'b::var_TT\<Rightarrow>'b" and R R' S S' x
  assumes "|supp u| <o bound(any::'a)" "|supp u'| <o bound(any::'a)"
    "bij v" "|supp v| <o bound(any::'b)" "bij v'" "|supp v'| <o bound(any::'b)"
  shows "map_F (u o u') (v o v') (f o f') (g o g') x = map_F u v f g (map_F u' v' f' g' x)"
  unfolding F_map_comp1[OF assms] by auto

lemma F_rel_map_: 
fixes u :: "'a::var_TT\<Rightarrow>'a" and v :: "'b::var_TT\<Rightarrow>'b"
assumes u: "|supp u| <o bound(any::'a)" 
and v: "bij v" "|supp v| <o bound(any::'b)"  
and r: "rrel_F R S x y"   
shows "rrel_F R S (map_F u v id id x) (map_F u v id id y)" 
  using r unfolding F_rel_map_set2_[OF u v]
  F_rel_map_set2_[OF supp_id_bound bij_id supp_id_bound, of R S, unfolded F_map_id, simplified] 
  apply safe
  subgoal for z apply(rule exI[of _ z]) 
  by (simp add: assms F_map_comp[symmetric] supp_id_bound) .

(**************)
(* Verifying the old axiomatization: *)
definition rel_F :: "('a :: var_TT \<Rightarrow> 'a) \<Rightarrow> ('b :: var_TT \<Rightarrow> 'b) \<Rightarrow> 
 ('c \<Rightarrow> 'c' \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('a,'b,'c,'d) F \<Rightarrow> ('a,'b,'c','d')F \<Rightarrow> bool"
  where "rel_F u v R S \<equiv> \<lambda> x x'. rrel_F R S (map_F u v id id x) x'"

lemma F_rel_id: "rel_F id id (=) (=) = (=)" 
  unfolding rel_F_def fun_eq_iff
  apply (auto simp only: F_rel_map_set2_ supp_id_bound OO_Grp_alt bij_id fst_conv snd_conv
    F_set3_map F_set4_map F_map_comp[symmetric] o_def id_apply id_def[symmetric]
    intro!: F_map_cong exI[of _ "map_F id id (\<lambda>x. (x, x)) (\<lambda>x. (x, x)) _"]
      trans[OF F_map_id[THEN fun_cong] id_apply])
  done
 
lemma F_rel_comp_leq:
fixes u u' ::"'a::var_TT\<Rightarrow>'a" and v v' :: "'b::var_TT\<Rightarrow>'b" and R R' S S'
assumes "|supp u| <o bound(any::'a)" and "|supp u'| <o bound(any::'a)"
and "bij v" and "|supp v| <o bound(any::'b)" and "bij v'" and "|supp v'| <o bound(any::'b)"
shows "rel_F u v R S OO rel_F u' v' R' S' \<le> rel_F (u' o u) (v' o v) (R OO R') (S OO S')" 
unfolding rel_F_def using F_rel_comp_leq_[of R S R' S'] 
using F_rel_map_[of u' v' R S "map_F u v id id _" _]
by (auto simp: assms F_map_comp[symmetric] supp_id_bound dest!: predicate2D) 
 
lemma F_rel_map_set2:
fixes u::"'a::var_TT\<Rightarrow>'a" and v::"'b::var_TT\<Rightarrow>'b" and R S x y
assumes u: "|supp u| <o bound(any::'a)" and v: "bij v" "|supp v| <o bound(any::'b)"
shows "rel_F u v R S x y \<longleftrightarrow>
   (\<exists>z. set3_F z \<subseteq> {(x, y). R x y} \<and> set4_F z \<subseteq> {(x, y). S x y} \<and> 
     map_F id id fst fst z = x \<and> map_F u v snd snd z = y)"  
unfolding rel_F_def F_rel_map_set2_[OF u v] ..  


(* SETUP FOR F *)

lemmas F_set_map = F_set1_map F_set2_map F_set3_map F_set4_map

(* Moved above, since needed for verifying the old axiomatization: *)
lemmas F_map_comp 

lemma F_rel_comp:
  fixes u u'::"'a::var_TT\<Rightarrow>'a" and v v' :: "'b::var_TT\<Rightarrow>'b" and R R' S S'
  assumes "|supp u| <o bound(any::'a)" "|supp u'| <o bound(any::'a)"
    "bij v" "|supp v| <o bound(any::'b)" "bij v'" "|supp v'| <o bound(any::'b)"
  shows "rel_F (u' o u) (v' o v) (R OO R') (S OO S') = rel_F u v R S OO rel_F u' v' R' S'"
  apply (rule antisym[OF predicate2I F_rel_comp_leq[OF assms]])
  apply (auto simp only: F_rel_map_set2 assms relcompp_apply supp_comp_bound bij_comp)
  subgoal for z
    apply (auto 0 4 simp only: F_set_map supp_id_bound supp_comp_bound bij_id F_map_comp[symmetric] assms o_id id_o
        o_apply fst_conv snd_conv bij_comp
        intro!: someI2_ex[of "\<lambda>b. R _ b \<and> R' b _" "\<lambda>b. R _ b"] someI2_ex[of "\<lambda>b. S _ b \<and> S' b _" "\<lambda>b. S _ b"]
        someI2_ex[of "\<lambda>b. R _ b \<and> R' b _" "\<lambda>b. R' b _"] someI2_ex[of "\<lambda>b. S _ b \<and> S' b _" "\<lambda>b. S' b _"]
        exI[of _ "map_F u v (\<lambda>(x, y). (SOME w. R x w \<and> R' w y, y)) (\<lambda>(x, y). (SOME w. S x w \<and> S' w y, y)) z"]
        exI[of _ "map_F id id (\<lambda>(x, y). (x, SOME w. R x w \<and> R' w y)) (\<lambda>(x, y). (x, SOME w. S x w \<and> S' w y)) z"]
        F_map_cong)
    done
  done

lemma F_rel_mono:
  fixes u ::"'a::var_TT\<Rightarrow>'a" and v :: "'b::var_TT\<Rightarrow>'b" and R R' S S'
  assumes bd: "|supp u| <o bound(any::'a)" "bij v" "|supp v| <o bound(any::'b)"
     and le:"R \<le> R'" "S \<le> S'"
  shows "rel_F u v R S \<le> rel_F u v R' S'"
  unfolding F_rel_map_set2[OF bd] using le
  by blast

lemma F_rel_Grp:
  fixes u ::"'a::var_TT\<Rightarrow>'a" and v :: "'b::var_TT\<Rightarrow>'b" and f g
  assumes "|supp u| <o bound(any::'a)" "bij v" "|supp v| <o bound(any::'b)"
  shows "rel_F u v (Grp f) (Grp g) = Grp (map_F u v f g)"
  apply (auto 0 3 simp only: F_rel_map_set2 fun_eq_iff Grp_def assms F_map_comp[symmetric] supp_id_bound bij_id o_id
    o_apply fst_conv snd_conv F_set_map id_apply
    intro!: F_map_cong  trans[OF F_map_cong fun_cong[OF F_map_id], THEN trans[OF _ id_apply]]
      exI[of _ "map_F id id (\<lambda>a. (a, f a)) (\<lambda>a. (a, g a)) _"])
  done

lemma F_rel_conversep:
  fixes u ::"'a::var_TT\<Rightarrow>'a" and v :: "'b::var_TT\<Rightarrow>'b" and R S
  assumes "bij u" "|supp u| <o bound(any::'a)" "bij v" "|supp v| <o bound(any::'b)"
  shows "rel_F (inv u) (inv v) (R\<inverse>\<inverse>) (S\<inverse>\<inverse>) = (rel_F u v R S)\<inverse>\<inverse>"
  apply (auto simp only: F_rel_map_set2 assms fun_eq_iff supp_inv_bound bij_imp_bij_inv)
  subgoal for z
    apply (auto simp only: F_rel_map_set2 assms fun_eq_iff supp_inv_bound bij_imp_bij_inv
      F_set_map F_map_comp[symmetric] supp_id_bound bij_id id_o fst_conv snd_conv o_apply
      supp_comp_bound bij_comp id_apply inv_simp2
      intro!: exI[of _ "map_F (inv u) (inv v) (\<lambda>(a, b). (b, a))  (\<lambda>(a, b). (b, a)) z"] F_map_cong)
    done
  subgoal for z
    apply (auto simp only: F_rel_map_set2 assms fun_eq_iff supp_inv_bound bij_imp_bij_inv
      F_set_map F_map_comp[symmetric] supp_id_bound bij_id id_o fst_conv snd_conv o_apply
      supp_comp_bound bij_comp id_apply inv_simp1
      intro!: exI[of _ "map_F u v (\<lambda>(a, b). (b, a))  (\<lambda>(a, b). (b, a)) z"] F_map_cong)
    done
  done

lemma F_rel_map_left:
  fixes u u'::"'a::var_TT\<Rightarrow>'a" and v v' :: "'b::var_TT\<Rightarrow>'b" and R f S g
  assumes "|supp u| <o bound(any::'a)" "|supp u'| <o bound(any::'a)"
    "bij v" "|supp v| <o bound(any::'b)" "bij v'" "|supp v'| <o bound(any::'b)"
  shows "rel_F u v R S (map_F u' v' f g b) b' =
       rel_F (u o u') (v o v') (Grp f OO R) (Grp g OO S) b b'"
  by (auto simp only: F_rel_comp assms F_rel_Grp relcompp_apply
    intro!: exI[where P="\<lambda>x. _ x \<and> _ x", OF conjI] GrpI elim!: GrpE)

lemma F_rel_map_right:
  fixes u u'::"'a::var_TT\<Rightarrow>'a" and v v' :: "'b::var_TT\<Rightarrow>'b" and R f S g
  assumes "|supp u| <o bound(any::'a)" "|supp u'| <o bound(any::'a)"
    "bij v" "|supp v| <o bound(any::'b)" "bij v'" "|supp v'| <o bound(any::'b)"
  shows "rel_F u' v' R S b b' \<Longrightarrow>
       rel_F (u o u') (v o v') (R OO Grp f) (S OO Grp g) b (map_F u v f g b')"
  by (auto simp only: F_rel_comp assms F_rel_Grp intro!: GrpI)

lemma F_rel_map_right_bij:
  fixes u u'::"'a::var_TT\<Rightarrow>'a" and v v' :: "'b::var_TT\<Rightarrow>'b" and R f S g
  assumes "|supp u| <o bound(any::'a)" "bij u'" "|supp u'| <o bound(any::'a)"
    "bij v" "|supp v| <o bound(any::'b)" "bij v'" "|supp v'| <o bound(any::'b)"
  shows "rel_F u v R S b (map_F u' v' f g b') =
       rel_F (inv u' o u) (inv v' o v) (R OO conversep (Grp f)) (S OO conversep (Grp g)) b b'"
  by (auto simp only: F_rel_comp assms F_rel_Grp supp_inv_bound bij_imp_bij_inv
    relcompp_apply F_map_comp[symmetric] inv_o_simp2 F_rel_conversep
    conversep_iff intro!: GrpI elim!: GrpE)

lemmas F_rel_map = F_rel_map_left F_rel_map_right F_rel_map_right_bij

lemma map_F_transfer:
  "rel_fun (eq_onp (\<lambda> u::'a::var_TT\<Rightarrow>'a. |supp u| <o bound(any::'a)))
    (rel_fun (eq_onp (\<lambda> v::'b::var_TT\<Rightarrow>'b. bij v \<and> |supp v| <o bound(any::'b)))
      (rel_fun (rel_fun R R') (rel_fun (rel_fun S S') (rel_fun (rel_F id id R S) (rel_F id id R' S'))))) map_F map_F"
  unfolding rel_fun_def eq_onp_def
  by (auto 0 3 simp only: F_rel_map_left supp_id_bound bij_id id_o relcompp_apply Grp_def
    elim!: predicate2D[OF F_rel_mono, rotated -1, OF F_rel_map_right, of _ id _ id, unfolded o_id, rotated 6])

lemma rel_F_transfer:
  "rel_fun (eq_onp (\<lambda> u::'a::var_TT\<Rightarrow>'a. |supp u| <o bound(any::'a)))
    (rel_fun (eq_onp (\<lambda> v::'b::var_TT\<Rightarrow>'b. bij v \<and> |supp v| <o bound(any::'b)))
      (rel_fun (rel_fun R (rel_fun R' (=))) (rel_fun (rel_fun S (rel_fun S' (=))) (rel_fun (rel_F id id R S) (rel_fun (rel_F id id R' S') (=)))))) rel_F rel_F"
  unfolding rel_fun_def eq_onp_def
  apply safe
  subgoal for _ u _ v P P' Q Q' b a c d
    apply (erule F_rel_mono[THEN predicate2D, rotated -1, OF F_rel_comp_leq[THEN predicate2D], of _ id _ id, rotated 6, OF relcomppI, unfolded id_o, rotated];
        (simp only: supp_id_bound bij_id)?)
      prefer 3
      apply (erule F_rel_mono[THEN predicate2D, rotated -1, OF F_rel_comp_leq[THEN predicate2D], of id _ id _, rotated 6, OF relcomppI, unfolded o_id, rotated];
        (simp only: supp_id_bound bij_id)?)
        prefer 3
    apply (erule F_rel_conversep[THEN predicate2_eqD, unfolded conversep_iff, THEN iffD2, of id id, unfolded inv_id, rotated -1];
        (simp only: supp_id_bound bij_id)?)
       apply (rule order_refl)+
     apply auto
    done
  subgoal for _ u _ v P P' Q Q' a b d c
    apply (erule F_rel_mono[THEN predicate2D, rotated -1, OF F_rel_comp_leq[THEN predicate2D], of id _ id _, rotated 6, OF relcomppI, unfolded o_id];
        (simp only: supp_id_bound bij_id)?)
      apply (erule F_rel_mono[THEN predicate2D, rotated -1, OF F_rel_comp_leq[THEN predicate2D], of _ id _ id, rotated 6, OF relcomppI, unfolded id_o];
        (simp only: supp_id_bound bij_id)?)
    apply (erule F_rel_conversep[THEN predicate2_eqD, unfolded conversep_iff, THEN iffD2, of id id, unfolded inv_id, rotated -1];
        (simp only: supp_id_bound bij_id)?)
       apply (rule order_refl)+
     apply auto
    done
  done

(* thm F.bd_card_order *)

bnf F: "('a::var_TT,'b::var_TT,'c,'d) F"
  map: "map_F id id :: _ \<Rightarrow> _ \<Rightarrow> ('a::var_TT,'b::var_TT,'c,'d) F \<Rightarrow> _"
  sets: "set3_F :: ('a::var_TT,'b::var_TT,'c,'d) F \<Rightarrow> _" "set4_F :: ('a::var_TT,'b::var_TT,'c,'d) F \<Rightarrow> _"
  bd: "bd_TT"  wits: "wit_F :: ('a::var_TT,'b::var_TT,'c,'d) F"
  rel: "rel_F id id  :: _ \<Rightarrow> _ \<Rightarrow> ('a::var_TT,'b::var_TT,'c,'d) F \<Rightarrow> _ \<Rightarrow> _"
  by (auto simp only: bd_TT_cinfinite bd_TT_card_order
      F_set_map[of id] F_rel_comp[of id _ id, simplified] F_rel_map_set2[of id id, simplified]
      fun_eq_iff F_set3_bd F_set4_bd ordLess_imp_ordLeq F_wit1 F_wit2 F_map_id
      supp_id_bound bij_id o_apply o_id F_map_comp[symmetric]
      intro!: F_map_cong) 

lemma F_rel_flip:
  fixes u ::"'a::var_TT\<Rightarrow>'a" and v :: "'b::var_TT\<Rightarrow>'b" and R S
  assumes "bij u" "|supp u| <o bound(any::'a)" "bij v" "|supp v| <o bound(any::'b)"
  shows "rel_F (inv u) (inv v) (conversep R) (conversep S) b b' \<longleftrightarrow> rel_F u v R S b' b"
  using F_rel_conversep[OF assms, of R S] by auto

lemma F_set_transfer:
  fixes u ::"'a::var_TT\<Rightarrow>'a" and v :: "'b::var_TT\<Rightarrow>'b" and R S
  assumes "|supp u| <o bound(any::'a)" "bij v" "|supp v| <o bound(any::'b)"
  shows
    F_set1_transfer: "rel_fun (rel_F u v R S) (Grp (image u)) set1_F set1_F" and
    F_set2_transfer: "rel_fun (rel_F u v R S) (Grp (image v)) set2_F set2_F" and
    F_set3_transfer: "rel_fun (rel_F u v R S) (rel_set R) set3_F set3_F" and
    F_set4_transfer: "rel_fun (rel_F u v R S) (rel_set S) set4_F set4_F"
  unfolding rel_fun_def rel_set_def Bex_def F_rel_map_set2[OF assms] Grp_def
  by (auto 0 4 simp only: F_set_map supp_id_bound bij_id assms id_apply image_id fst_conv snd_conv)

lemma F_rel_mono_strong0:
  fixes u u'::"'a::var_TT\<Rightarrow>'a" and v v' :: "'b::var_TT\<Rightarrow>'b" and R R' S S'
  assumes uv: "|supp u| <o bound(any::'a)" "|supp u'| <o bound(any::'a)"
    "bij v" "|supp v| <o bound(any::'b)" "bij v'" "|supp v'| <o bound(any::'b)"
    and rel: "rel_F u v R S x y"
    and set1:"\<forall>a\<in>set1_F x. u a = u' a"
    and set2:"\<forall>a\<in>set2_F x. v a = v' a"
    and set3:"\<forall>c1\<in>set3_F x. \<forall>c2\<in>set3_F y. R c1 c2 \<longrightarrow> R' c1 c2"
    and set4:"\<forall>d1\<in>set4_F x. \<forall>d2\<in>set4_F y. S d1 d2 \<longrightarrow> S' d1 d2"
  shows "rel_F u' v' R' S' x y"
  using rel set1 set2 set3 set4
  apply (auto simp only: F_rel_map_set2 uv)
  subgoal for z
    apply (auto simp only: uv F_set_map supp_id_bound bij_id image_id id_apply
      intro!: exI[of _ z] F_map_cong)
     apply fastforce+
    done
  done

lemma F_rel_mono_strong1:
  fixes u ::"'a::var_TT\<Rightarrow>'a" and v :: "'b::var_TT\<Rightarrow>'b" and R R' S S'
  assumes u: "|supp u| <o bound(any::'a)" and v: "bij v" "|supp v| <o bound(any::'b)"
    and rel: "rel_F u v R S x y"
    and set3:"\<forall>c1\<in>set3_F x. \<forall>c2\<in>set3_F y. R c1 c2 \<longrightarrow> R' c1 c2"
    and set4:"\<forall>d1\<in>set4_F x. \<forall>d2\<in>set4_F y. S d1 d2 \<longrightarrow> S' d1 d2"
  shows "rel_F u v R' S' x y"
  by (rule F_rel_mono_strong0[OF u u v v rel _ _ set3 set4]) simp_all
  
(* Some transfer setup  *)
  
definition rel_F_id :: "('c \<Rightarrow> 'c' \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'd' \<Rightarrow> bool) \<Rightarrow> ('a::var_TT, 'b::var_TT, 'c, 'd) F \<Rightarrow> ('a, 'b, 'c', 'd') F \<Rightarrow> bool"
  where "rel_F_id = rel_F id id"
    
lemma left_total_rel_F_id[transfer_rule]:
  "left_total R \<Longrightarrow> left_total S \<Longrightarrow> left_total (rel_F_id R S)"
  
  unfolding left_total_alt_def rel_F_id_def F.rel_conversep[symmetric]
    F.rel_eq[symmetric] F.rel_compp[symmetric]  
   by (rule F.rel_mono)  
   
lemma right_total_rel_F_id[transfer_rule]:
  "right_total R \<Longrightarrow> right_total S \<Longrightarrow> right_total (rel_F_id R S)"
  unfolding right_total_alt_def rel_F_id_def F.rel_conversep[symmetric]
    F.rel_eq[symmetric] F.rel_compp[symmetric]
  by (rule F.rel_mono)

lemma bi_total_rel_F_id[transfer_rule]: "bi_total R \<Longrightarrow> bi_total S \<Longrightarrow> bi_total (rel_F_id R S)"
  unfolding bi_total_alt_def using left_total_rel_F_id right_total_rel_F_id by blast

declare F.map_transfer[folded rel_F_id_def, transfer_rule]
declare F.set_transfer[folded rel_F_id_def, transfer_rule]
declare F_set1_transfer[OF supp_id_bound bij_id supp_id_bound, unfolded image_id, folded rel_F_id_def eq_alt, transfer_rule]
declare F_set2_transfer[OF supp_id_bound bij_id supp_id_bound, unfolded image_id, folded rel_F_id_def eq_alt, transfer_rule]

(* ``as small support'' cast operator *)
definition asSS :: "('a::var_TT \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "asSS f \<equiv> if |supp f| <o bound(any::'a) then f else id"

end