theory Card_Prelim
  imports "HOL-Cardinals.Cardinals"
begin

lemma card_of_Un_eq_Plus:
assumes "A \<inter> B = {}"
shows "|A \<union> B| =o |A <+> B|"
proof(rule card_of_ordIsoI)
  show "bij_betw (\<lambda> a. if a \<in> A then Inl a else Inr a) (A \<union> B) (A <+> B)"
    using assms unfolding bij_betw_def inj_on_def by auto
qed

lemma infinite_card_of_minus:
  assumes i: "infinite A" and b: "|B| <o |A|" and bi: "B \<subseteq> A"
  shows "|A - B| =o |A|"
proof-
  {assume "|A - B| <o |A|"
    hence "|(A - B) <+> B| <o |A|" using b card_of_Plus_ordLess_infinite[OF i] by auto
    moreover have "|A| \<le>o |(A - B) <+> B|"
      using card_of_Un_Plus_ordLeq[of "A - B" B] bi by (metis Diff_partition Un_commute)
    ultimately have False using not_ordLess_ordLeq by blast
  }
  moreover have  "|A - B| \<le>o |A|" by (simp add: Diff_subset)
  ultimately show ?thesis using ordLeq_iff_ordLess_or_ordIso by blast
qed

lemma infinite_UNIV_card_of_minus:
  assumes i: "infinite (UNIV::'a set)" and b: "|B::'a set| <o |UNIV::'a set|"
  shows "|UNIV - B| =o |UNIV::'a set|"
  using infinite_card_of_minus[OF assms] by auto

lemma regularCard_Un:
assumes "Card_order r" and "cinfinite r" and "regularCard r"
 and "|A1| <o r" and "|A2| <o r"
shows "|A1 \<union> A2| <o r"
  using assms card_of_Un_ordLess_infinite_Field cinfinite_def by blast

lemma regularCard_UNION:
assumes "Card_order r" "cinfinite r" "regularCard r"
and "|I| <o r" "\<And>i. i \<in> I \<Longrightarrow> |A i| <o r"
shows "|\<Union>i\<in>I. A i| <o r"
  using assms cinfinite_def regularCard_stable stable_UNION by blast
 
lemma cardSuc_ordLeq_pow:
  assumes "Card_order (k:: 'b rel)"  
  shows "cardSuc k \<le>o |UNIV:: 'b set set|"
by (intro cardSuc_least) (auto simp : assms cardSuc_ordLess_ordLeq)
    
lemma regularCard_ordIso:
assumes  "Card_order k" "cinfinite k" and "Card_order k'" "cinfinite k'"  and "k =o k'" and "regularCard k"
shows "regularCard k'"
proof-
  have "stable k" using assms cinfinite_def regularCard_stable by blast
  hence "stable k'" using assms stable_ordIso by blast
  thus ?thesis using assms cinfinite_def stable_regularCard by blast
qed

lemma bij_card_of_ordIso: 
  assumes "bij f" shows "|f ` A| =o |A|"
proof-
  have "bij_betw f A (f ` A)" using assms unfolding bij_def bij_betw_def inj_on_def surj_def by auto
  thus ?thesis
  using card_of_ordIso bij_betw_inv by blast
qed

(* Get the cardinal successor so that it is covers an 
 entire type: *)
typedef 'a csuc = "Field (cardSuc |UNIV::'a set| )" 
  by (simp add: Field_cardSuc_not_empty ex_in_conv) 

definition cardSuc2 :: "'a rel \<Rightarrow> ('a csuc) rel" where 
"cardSuc2 r \<equiv> |UNIV|" 
 
lemma card_order_cardSuc2: 
assumes "card_order r"
shows "card_order (cardSuc2 r)"
  by (simp add: cardSuc2_def)

lemma Card_order_cardSuc2:
"card_order r \<Longrightarrow> Card_order (cardSuc2 r)"
  by (simp add: cardSuc2_def)

lemma cardSuc2_cardSuc:
assumes "card_order r"
shows "cardSuc2 r =o cardSuc r" 
proof-
  term bij_betw
  have 0: "bij_betw Rep_csuc 
         (UNIV::('a csuc) set) 
         (Field (cardSuc |UNIV::'a set| ))"
  unfolding bij_betw_def 
  by (meson Rep_csuc_inject inj_on_def type_definition.Rep_range 
     type_definition_csuc)
  have "cardSuc2 r =o |Field (cardSuc |UNIV::'a set| )|" 
  unfolding cardSuc2_def card_of_ordIso[symmetric] 
  using 0 by auto 
  also have "|Field (cardSuc |UNIV::'a set| )| =o 
             cardSuc |UNIV::'a set|" 
  by simp
  also have "cardSuc |UNIV::'a set| =o cardSuc r"
  using assms card_of_Field_ordIso card_order_on_Card_order by fastforce
  finally show ?thesis .
qed

(* Borrowing theorems from cardSuc: *) 
lemma Cinfinite_cardSuc2: 
"cinfinite r \<Longrightarrow> card_order r \<Longrightarrow> cinfinite (cardSuc2 r)" 
  by (metis Field_card_of Field_card_order cardSuc2_cardSuc cardSuc2_def cardSuc_finite card_of_ordIso_finite card_of_unique card_order_cardSuc2 
  cinfinite_def ordIso_finite_Field)

lemma infinite_cardSuc2_regularCard: 
"infinite (Field r) \<Longrightarrow> card_order r \<Longrightarrow> regularCard (cardSuc2 r)"
apply(rule regularCard_ordIso[of "cardSuc r"]) 
  apply (simp add: Field_card_order)  
  apply (simp add: Field_card_order cinfinite_def)
  apply (simp add: cardSuc2_def)  
  using Cinfinite_cardSuc2 cinfinite_def apply auto[1]
  using cardSuc2_cardSuc ordIso_symmetric apply auto[1]
  by (simp add: Field_card_order infinite_cardSuc_regularCard)

end