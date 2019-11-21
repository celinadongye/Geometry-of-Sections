theory Practical
imports Main
begin

(***************************First-order logic*************************************)

(*1 mark*)
lemma "A\<or>A \<longrightarrow> A"
  apply (rule impI)
  apply (erule disjE)
   apply assumption+
  done

(*1 mark*)
lemma "(P\<longrightarrow>R)\<longrightarrow>(\<not>P\<or>R)"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply (rule ccontr)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

(*1 mark*)
lemma "(P\<and>Q\<longrightarrow>R)\<longrightarrow>P\<longrightarrow>Q\<longrightarrow>R"
  apply (rule impI)+
  apply (erule impE)
   apply (rule conjI)
    apply assumption+
  done

(*3 marks*)
lemma "\<not>\<not>P \<or> \<not>P"
  apply (rule classical)
  apply (rule disjI2)
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI1)
  apply assumption
  done

(*4 marks*)
lemma "(P\<or>R)\<longleftrightarrow>(\<not>(\<not>P\<and> \<not>R))"
  apply (rule iffI)
   apply (rule notI)
   apply (erule disjE)
    apply (erule conjE)
    apply (erule notE)
    apply assumption
   apply (erule conjE)
   apply (erule_tac P = "R" in notE)
   apply assumption
  apply (rule ccontr)
  apply (erule notE)
  apply (rule conjI)
   apply (rule notI)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

(*1 mark*)
(* First version theory file lemma *)
lemma "(\<forall> x . F x \<longrightarrow> G x ) \<longrightarrow> \<not> (\<exists> x . F x \<and> \<not> G x )"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule allE)
  apply (erule impE)
   apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  done
(* Lemma in handout *)
lemma "(\<forall> x . F x) \<and> (\<forall> x . G x ) \<longrightarrow> (\<forall> x . F x \<and> G x )"
  apply (rule impI)
  apply (rule allI)
  apply (erule conjE)
  apply (rule conjI)
   apply (erule allE, assumption)+
  done

(*1 mark*)
lemma "(\<forall> x y. R x y) \<longrightarrow> (\<forall> x . R x x )"
  apply (rule impI)
  apply (rule allI)
  apply (erule allE)+
  apply assumption
  done

(*3 marks*)
lemma "(\<forall>x. P x)\<or>(\<exists>x.\<not>P x)"
(* avoid using classical *)
  apply (rule classical)
  apply (rule disjI1)
  apply (rule classical)
  apply (rule allI)
  apply (erule notE)
  apply (rule disjI2)
  apply (rule classical)
  apply (rule exI)
  apply (rule notI)
  apply (erule notE)
  apply (rule allI)
  apply (rule classical)
  apply (erule notE)
  apply (rule exI)
  apply (rule notI)
  apply (erule notE)
  apply assumption
  done

(*3 marks*)
lemma "(\<forall>x. \<not> (P x \<longrightarrow> Q x)) \<longrightarrow> \<not>(\<exists>x. \<not>P x \<and> Q x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule allE)
  apply (erule notE)
  apply (rule impI)
  apply (erule conjE)
  apply assumption
  done

(*3 marks*)
lemma "\<exists>Bob. (drunk Bob \<longrightarrow> (\<forall>y. drunk y))"
 apply (rule classical)
  apply (rule exI)
  apply (rule impI)
  apply (rule allI)
  apply (erule notE)
  apply (rule classical)
  apply (rule exI)
  apply (rule impI)
  apply (rule allI)
  apply (rule classical)
  apply (erule notE)
  apply (rule exI)
  apply (rule impI)
  apply (rule allI)
  apply (erule notE)
  apply assumption
  done

(*4 marks*)
lemma "\<not> (\<exists> barber . man barber \<and> (\<forall> x . man x \<and> \<not>shaves x x \<longleftrightarrow> shaves barber x ))"
  apply (rule notI)
  apply (erule exE)
  apply (erule conjE)
  apply (erule allE)
  apply (erule iffE)
  apply (erule impE)
   apply (rule conjI)
    apply assumption
   apply (rule notI)

   apply (erule impE, assumption, erule conjE, erule notE, assumption)+
  done

locale incidence =
  fixes incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" (infix " \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t " 80)
  fixes region_to_section :: "'region \<Rightarrow> 'section" 
(*Write here your axiom stating that every section has a point incident to it*) (*2 marks*)
  assumes section_nonempty: "\<forall>s. \<exists>P. P \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s"
(*Write here your axiom stating that two sections are the same
                                      if the same points are incident to each*) (*2 marks*)
  and section_uniqueness: "\<forall>s1 s2. (\<forall>P. (P \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s1 \<longleftrightarrow> P \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s2)) \<longrightarrow> s1 = s2"

begin

definition isPartOf ::"'section \<Rightarrow> 'section \<Rightarrow> bool" (infix "isPartOf" 80) where 
(*write your formalisation of definition D1 here*) (*1 mark*)
"s1 isPartOf s2 \<equiv> \<forall>P. (P \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s1 \<longrightarrow> P \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s2)"

definition inclusion ::"'region \<Rightarrow> 'section \<Rightarrow> bool"(infix "isIncludedIn" 80) where
(*write your formalisation of definition D2 here*) (*1 mark*)
"R isIncludedIn s \<equiv> (region_to_section R) isPartOf s"

definition overlaps ::"'region \<Rightarrow> 'section \<Rightarrow> bool"(infix "overlaps" 80) where
(*write your formalisation of definition D3 here*) (*1 mark*)
" R overlaps s \<equiv> \<exists>P. P \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t (region_to_section R) \<and> P \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t s"

lemma region_overlaps_itself: "R overlaps (region_to_section R)"
(*Write your structured proof here*) (*2 marks*)
proof (unfold overlaps_def)
  have incidence: "\<exists>P. P \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t region_to_section R"
    by (simp add: section_nonempty)
  show "\<exists>P. P  \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t  region_to_section R \<and> P  \<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t  region_to_section R" using incidence
    by auto
qed 

(*Formalise and prove that isPartOf is reflexive, transitive and antisymmetric*) (*3 marks*)
lemma isPartOf_reflexive: "s isPartOf s"
(*Formalise and prove that isPartOf is reflexive here*)
  by (simp add: isPartOf_def)

lemma isPartOf_transitive: "(s1 isPartOf s2 \<and> s2 isPartOf s3) \<longrightarrow> s1 isPartOf s3"
(*Formalise and prove that isPartOf is transitive here*)
  by (simp add: isPartOf_def)

lemma isPartOf_antisymmetric: "(s1 isPartOf s2 \<and> s2 isPartOf s1) \<longrightarrow> s1 = s2"
(*Formalise and prove that isPartOf is antisymmetric here*)
  using isPartOf_def section_uniqueness by blast
end


locale section_bundles =  incidence incidence_points_on_sections region_to_section 
  for  incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" 
  and region_to_section :: "'region \<Rightarrow> 'section" +
  fixes crossing :: "'region \<Rightarrow> 'section \<Rightarrow> bool" 
  and incidence_sections_on_bundles :: "'section \<Rightarrow> 'bundle \<Rightarrow> bool" (infix "\<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n" 80) 
(*Write your formalisation of Axiom SC1 here*) (*1 mark*)
  assumes SC1: "\<forall>s R. (crossing R s) \<longrightarrow> (R overlaps s)"
(*Write your formalisation of Axiom SI1 here*)     (*1 mark*)
 and SI1: "\<forall>s b1 b2. (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b1 \<longleftrightarrow> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b2) \<longrightarrow> (b1 = b2)"

begin

definition atLeastAsRestrictiveAs :: "'section \<Rightarrow> 'bundle \<Rightarrow> 'section \<Rightarrow> bool" where 
(*Write your formalisation of atLeastAsRestrictiveAs here*) (*1 mark*)
"atLeastAsRestrictiveAs s1 b s2 \<equiv> (s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s1 isPartOf s2)"

notation 
  atLeastAsRestrictiveAs ("_ \<le>\<^sub>_ _" [80, 80, 80] 80)


(*Formalise and prove that isPartOf is reflexive, transitive and antisymmetric*) (*2 marks*)

(*Kulik and Eschenbach say 'The relation \<ge> is reflexive, transitive and antisymmetric for a given 
sector bundle.' So, do they mean, given that the sections under consideration are in the bundle?
This is what we assume for reflexivity.*)
lemma atLeastAsRestrictiveAs_reflexive: 
  assumes "s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"  shows "s \<le>\<^sub>b s"
(*Add your proof here*)
  by (simp add: assms atLeastAsRestrictiveAs_def isPartOf_reflexive)

lemma atLeastAsRestrictiveAs_transitive: 
(*Formalise and prove that atLeastAsRestrictiveAs is transitive*)
  assumes "s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b" shows "(s1 \<le>\<^sub>b s2 \<and> s2 \<le>\<^sub>b s3) \<longrightarrow> (s1 \<le>\<^sub>b s3)"
  using atLeastAsRestrictiveAs_def isPartOf_transitive by blast

lemma atLeastAsRestrictiveAs_antisymmetric: 
(*Formalise and prove that atLeastAsRestrictiveAs is antisymmetric*)
  assumes "s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b" shows "(s1 \<le>\<^sub>b s2 \<and> s2 \<le>\<^sub>b s1) \<longrightarrow> (s1 = s2)"
  by (simp add: atLeastAsRestrictiveAs_def isPartOf_antisymmetric)

end


locale comparison = section_bundles incidence_points_on_sections region_to_section 
 crossing incidence_sections_on_bundles
  for  incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" (infix "\<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t" 80) 
  and region_to_section :: "'region \<Rightarrow> 'section" 
  and crossing :: "'region \<Rightarrow> 'section \<Rightarrow> bool" (infix "crosses" 80) 
  and incidence_sections_on_bundles :: "'section \<Rightarrow> 'bundle \<Rightarrow> bool" (infix "\<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n" 80)+
(*Write your formalisation of Axiom SB2 here*) (*1 mark*)
assumes SB2: "\<forall>b s1 s2. (s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<longrightarrow> (s1 \<le>\<^sub>b s2 \<or> s2 \<le>\<^sub>b s1)"

begin

(*Write your formalisation and proof of Theorem T1 here*) (*1 mark*)
lemma T1: "\<forall>b s1 R. (R overlaps s1) \<longrightarrow> (\<forall>s2. (s1 \<le>\<^sub>b s2) \<longrightarrow> (R overlaps s2))"
  using atLeastAsRestrictiveAs_def isPartOf_def overlaps_def by auto

(*Write your formalisation and proof of Theorem T2 here*) (*1 mark*)
lemma T2: "\<forall>b s1 R. (R isIncludedIn s1) \<longrightarrow> (\<forall>s2. (s1 \<le>\<^sub>b s2) \<longrightarrow> (R isIncludedIn s2))"
  using atLeastAsRestrictiveAs_def inclusion_def isPartOf_transitive by blast

thm inclusion_def

definition isCore (infix "isCoreOf" 80) where
"s isCoreOf b = (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (\<forall>s'. s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s \<le>\<^sub>b s'))"

(*Write your definition of hull here*) (*1 mark*)
definition isHull (infix "isHull" 80) where
"s isHull b = (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (\<forall>s'. s' \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s' \<le>\<^sub>b s))"

end


locale crossing_sector = comparison incidence_points_on_sections 
          region_to_section crossing incidence_sections_on_bundles
          for incidence_points_on_sections :: "'point \<Rightarrow> 'section \<Rightarrow> bool" (infix "\<iota>\<^sub>p\<^sub>o\<^sub>i\<^sub>n\<^sub>t" 80) 
and region_to_section :: "'region \<Rightarrow> 'section" 
and crossing :: "'region \<Rightarrow> 'section \<Rightarrow> bool" (infix "crosses" 80)  
and incidence_sections_on_bundles :: "'section \<Rightarrow> 'bundle \<Rightarrow> bool" (infix "\<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n" 80) +
(*Write your formalisation of Axiom SC2 here*) (*1 mark*)
assumes SC2: "\<forall>b s1 R. (R crosses s1) \<longrightarrow> (\<forall>s2. (s2 \<le>\<^sub>b s1) \<longrightarrow> (R crosses s2))"
begin

(****************************)
(*Write your formalisation and structured proof of the remark 'If a region 
overlaps the core of a section bundle then it overlaps every section of the section bundle'*) 
(*4 marks*)
lemma overlaps_core:
  assumes core: "s1 isCoreOf b" and overlap: "R overlaps s1"
  shows "\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R overlaps s"
proof (rule allI, rule impI)
  fix s
  assume "s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"
  then have "s1 \<le>\<^sub>b s"
    using core isCore_def by blast
  then show "R overlaps s"
    using overlap T1 by blast
qed

(*
We have that section s is core of bundle b, and region R overlaps s.
We showed that s is a section of b, by the definition of core (which says that this section contains
all sections in the bundle.
We need to show that for all sections of the bundle (part of the bundle), we have that R overlaps
all these sections from the theorems we proved previously (core_region)
 *)


(*Write your formalisation and structured proof of the remark `If a region 
crosses the hull of a section bundle then it crosses every sector of the section bundle'*) 
(*4 marks*)
lemma crosses_hull:
  assumes hull: "s1 isHull b" and cross: "R crosses s1"
  shows "\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R crosses s"
proof (rule allI, rule impI)
  fix s
  assume "s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"
  then have "s \<le>\<^sub>b s1"
    using hull isHull_def by blast
  then show "R crosses s"
    using cross SC2 by blast
qed


(*Write your formalisation and structured proof of the remark `If a region 
does not overlap the hull of a section bundle, it does not overlap any of its sections'*) 
(*4 marks*)
lemma not_overlap_hull:
  assumes hull: "s1 isHull b" and not_overlaps: "\<not>(R overlaps s1)" and section_bundle: "s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"
  shows "(\<not>(R overlaps s))"
proof (insert not_overlaps, rule contrapos_nn, assumption)
  assume all_overlaps: "R overlaps s"
  then have "s \<le>\<^sub>b s1"
    using hull isHull_def section_bundle by blast
  then show "R overlaps s1"
    using not_overlaps all_overlaps T1 by blast
qed


definition overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  where 
"overlapsAsMuchAs R b R' == (\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R' overlaps s \<longrightarrow> R overlaps s)"

notation 
  overlapsAsMuchAs ("_ \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)

definition eq_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  where 
"eq_overlapsAsMuchAs R b R' == R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R"

notation 
  eq_overlapsAsMuchAs ("_ \<cong>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)

abbreviation
rev_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  ("_ \<le>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)
where"rev_overlapsAsMuchAs R b R' == overlapsAsMuchAs R' b R"

definition more_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  where 
"more_overlapsAsMuchAs R b R' == R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R' \<and> \<not>(R' \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R)"

notation 
  more_overlapsAsMuchAs ("_ >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)

abbreviation
less_overlapsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool"  ("_ <\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>_ _" [80, 80, 80] 80)
where"less_overlapsAsMuchAs R b R' == more_overlapsAsMuchAs R' b R"

(*Formalise and prove that overlapsAsMuchAs is reflexive and transitive*) (*2 marks*)

lemma overlapsAsMuchAs_reflexive:
(*Write your formalisation and proof that overlapsAsMuchAs is reflexive here*) 
  assumes "s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b" shows "R1 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R1"
  by (simp add: overlapsAsMuchAs_def)

lemma overlapsAsMuchAs_transitive:
(*Write your formalisation and proof that overlapsAsMuchAs is transitive here*)
  assumes "s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b" shows "(R1 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2 \<and> R2 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R3) \<longrightarrow> (R1 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R3)"
  by (simp add: overlapsAsMuchAs_def)


(*Write your formalisation and structured proof of Theorem T3 here. You must attempt to 
formalise Kulik et al.'s reasoning*) (*11 marks*)
lemma T3: "\<forall>b R1 R2. (R1 >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2) \<longleftrightarrow> (\<exists>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R1 overlaps s \<and> \<not>(R2 overlaps s))"
proof ((rule allI)+, rule iffI)
  fix b R1 R2
(*Left-to-right \<Rightarrow>*)
  assume moreThan: "R1 >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2"
  then have asMuchAs: "R1 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2"
    by (simp add: more_overlapsAsMuchAs_def)
  then have not_asMuchAs: "\<not>(R2 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R1)"
    using more_overlapsAsMuchAs_def moreThan by blast
(*overlaps as much as definition*)
  obtain s where ov_def: "s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R2 overlaps s \<longrightarrow> R1 overlaps s"
                and not_ov_def: "\<not>(s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> R1 overlaps s \<longrightarrow> R2 overlaps s)"
    using not_asMuchAs overlapsAsMuchAs_def by blast
  then have overlaps: "R1 overlaps s"
    by blast
  then have not_overlaps: "\<not>(R2 overlaps s)"
    using not_ov_def by blast
  then have "(\<not>(s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b) \<or> R1 overlaps s) \<and> \<not>(R2 overlaps s)" (*Equivalent to not_ov_def*)
    using not_ov_def by blast
  then show "\<exists>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R1 overlaps s \<and> \<not>(R2 overlaps s)"
    using not_ov_def by blast
next
(*Right-to-left \<Leftarrow>*)
  fix b R1 R2
  assume "(\<exists>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> R1 overlaps s \<and> \<not>(R2 overlaps s))"
  then obtain s1 where section_bundle1: "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b" and overlaps1: "R1 overlaps s1"
                       and not_overlaps1: "\<not>(R2 overlaps s1)"
    by blast
  then obtain s2 where section_bundle2: "s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b" 
    by blast
  then have "(s1 \<le>\<^sub>b s2 \<or> s2 \<le>\<^sub>b s1)"
    using SB2 section_bundle1 by auto
  then have restrictive: "s1 \<le>\<^sub>b s2 \<or> s2 \<le>\<^sub>b s1"
    using section_bundle1 section_bundle2 by blast
 (* then have part_of: "(s1 isPartOf s2) \<or> (s2 isPartOf s1)"
    using atLeastAsRestrictiveAs_def by blast*)
  (*Proof by cases*)
  from restrictive consider "s1 \<le>\<^sub>b s2" | "s2 \<le>\<^sub>b s1" by auto
  then have asMuchAs: "R1 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2"
  proof (cases)
    assume res1: "s1 \<le>\<^sub>b s2"
    then have "(R1 overlaps s1) \<longrightarrow> (s1 \<le>\<^sub>b s2) \<longrightarrow> (R1 overlaps s2)"
      using T1 by blast
    then have overlaps2: "R1 overlaps s2"
      using overlaps1 res1 by blast
    then show "R1 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2"
      using SB2 T1 not_overlaps1 overlaps1 overlapsAsMuchAs_def section_bundle1 by blast
  next
    assume res2: "s2 \<le>\<^sub>b s1"
    then have expanded_t1: "(\<not>(R2 overlaps s1) \<or> (s2 \<le>\<^sub>b s1)) \<and> \<not>(R2 overlaps s2)"
      using T1 not_overlaps1 by blast
    then have not_overlaps2: "\<not>(R2 overlaps s2)"
      by blast
    then show "R1 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2"
      using SB2 T1 not_overlaps1 overlaps1 overlapsAsMuchAs_def section_bundle1 by blast
  qed
  have not_asMuchAs: "\<not>(R2 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R1)"
    using section_bundle1 overlaps1 not_overlaps1 overlapsAsMuchAs_def by blast
  then have "R1 >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2"
    by (simp add: asMuchAs more_overlapsAsMuchAs_def not_asMuchAs)
  then show "R1 >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2"
    by blast
qed

(*In under 200 words, compare and contrast the mechanical proof that you produced with the 
pen-and-paper proof by Kulik et al.\. In particular, indicate any reasoning, proof parts, and/or 
useful lemmas that you had to make explicit during the mechanisation but may have been glossed over
 or assumed by the pen-and-paper proof. Also highlight any inaccuracies in their language or 
notation. Note any parts where you had to diverge from their reasoning, and why.
Write your answer in a comment here.*) (*4 marks*)

(*
LEFT-TO-RIGHT \<Rightarrow>
In my paper proof, I just assumed I had an 's' and didn't consider having to get a specific 's' for
the \<exists>s in the conclusion. So, my paper proof was very simple, where I expanded R1 > R2 by the
definition of more_overlapsAsMuchAs in order to obtain R1 \<ge> R2 and \<not>(R2 \<ge> R1). Then, I expanded
both of these expressions using the definition of overlapsAsMuchAs to get 'R1 overlaps s' and
'\<not>(R2 overlaps s)' respectively, both of which are in the conclusion.
However, for my Isabelle proof, I had to explicitly obtain section 's' using the constraints imposed
by the definition of overlapsAsMuchAs in order to prove the conclusion. I had to make explicit the 
the definition of overlapsAsMuchAS to get 'R1 overlaps s' and '\<not>(R2 overlaps s)'.

RIGHT-TO-LEFT \<Leftarrow>
For this proof I followed Kulik et al.'s reasoning. One of the incaccuracies is that they mentioned
getting 's1 isPartOf s2 \<or> s2 isPartOf s1' using SB2, but these expressions didn't help me in the
proof. Instead, I used atLeastAsRestrictiveAs in order to obtain the regions overlapping the sections
using T1. That is, I had to do a proof by cases using 's1 \<le>\<^sub>b s2' and 's2 \<le>\<^sub>b s1' separately.
For proving 'R1 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2', I had to explicitly indicate that I was using lemma T1 and
axiom SB2, not only T1 as stated by Kulik. In my mechanical proof, I also had to make explicit that
I had '\<not>(R2 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R1)' from '\<not>(R2 overlaps s)' to obtain the conclusion.
*)

(*Write your formalisation and proof of Theorem T4 here*) (*1 mark*)
lemma T4: "\<forall>b R1 R2. (R1  >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2) \<or> (R1 \<cong>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2) \<or> (R1 <\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2)"
proof -
  show "\<forall>b R1 R2. (R1  >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2) \<or> (R1 \<cong>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2) \<or> (R1 <\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2)"
    using T3 eq_overlapsAsMuchAs_def overlapsAsMuchAs_def by auto
qed

(*Write your formalisation and structured proof of Theorem T5 here. 
You must show it follows from T4*) (*3 marks*)
lemma T5: "\<forall>b R1 R2. (R1 \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2) \<or> (R1 \<le>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2)"
proof (rule allI)+
  fix b R1 R2
  show "R2 \<le>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R1 \<or> R1 \<le>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2"
    using T4 eq_overlapsAsMuchAs_def more_overlapsAsMuchAs_def by blast
(*(R1  >\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2) \<or> (R1 \<cong>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2) \<or> (R1 <\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R2)*)
qed


(********************Challenge problem****************************************)

(*Write your definition of the relation ci here. 
Kulik et al. say `If a region crosses or is included in a section we write ci'.*) (*2 marks*)
definition crosses_isIncludedIn :: "'region \<Rightarrow> 'section \<Rightarrow> bool"  where
"crosses_isIncludedIn R s \<equiv> R crosses s \<or> R isIncludedIn s"

notation 
  crosses_isIncludedIn ("_ ci _" 80)

(*Write your definition of `crosses or is included in as much as' here*) (*2 marks*)
definition crosses_isIncludedInAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool" where
"crosses_isIncludedInAsMuchAs R b R' \<equiv> (\<forall>s. s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> (R crosses s \<or> (R' isIncludedIn s \<longrightarrow> R isIncludedIn s)))" 

notation 
  crosses_isIncludedInAsMuchAs ("_ \<ge>\<^sub>c\<^sub>i \<^sub>_ _" [80, 80, 80] 80)

(*Write your definition of `belongs as much as here: definition D8 in the paper.*) (*2 marks*)
definition belongsAsMuchAs :: "'region \<Rightarrow> 'bundle \<Rightarrow> 'region \<Rightarrow> bool" where
"belongsAsMuchAs R b R' \<equiv>  (R \<ge>\<^sub>c\<^sub>i \<^sub>b R') \<and> (R \<ge>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R')"

notation 
  belongsAsMuchAs ("_ \<ge> \<^sub>_ _" [80, 80, 80] 80)

(*Formalise and write structured proofs of Theorems T6-T8 for both crossesIncludedInAsMuchAs and
belongsAsMuchAs*) (*14 marks*)

lemma T6_crosses_isIncludedInAsMuchAs: "\<forall>b R1. (\<exists>s. s isHull b \<and> \<not>(R1 overlaps s)) \<longrightarrow> (\<forall>R2. R2 \<ge>\<^sub>c\<^sub>i \<^sub>b R1)"
proof ((rule allI)+, rule impI, rule allI)
  fix b R1 R2 
  assume "\<exists>s. s isHull b \<and> \<not>(R1 overlaps s)"
  then obtain s1 where hull: "s1 isHull b" and not_overlaps: "\<not>(R1 overlaps s1)"
    by blast
  then have hull_def: "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<and> (\<forall>s2. s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<longrightarrow> s2 \<le>\<^sub>b s1)"
    using hull isHull_def by blast
  then have section_bundle: "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"
    by blast
  then show "R2 \<ge>\<^sub>c\<^sub>i \<^sub>b R1"
    by (meson crosses_isIncludedInAsMuchAs_def hull inclusion_def isPartOf_def not_overlap_hull
        not_overlaps overlaps_def region_overlaps_itself)
qed
(*
  assume "s2 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"
  then have res: "s2 \<le>\<^sub>b s1"
    using hull_def by blast
  then have "s2 isPartOf s1"
    by (simp add: atLeastAsRestrictiveAs_def)
  then have part: "(region_to_section R2) isPartOf s1" (*s2 = region_to_section R2*)
    by (simp add: eq)
  then have inclusion1: "R2 isIncludedIn s1"
    by (simp add: inclusion_def)
  then have not_crosses: "\<not>(R1 crosses s1)" (*\<^sub>c\<^sub>iconclusion of \<ge>\<^sub>c\<^sub>i: R1 crosses s1 \<or> (R2 isIncludedIn s1 \<longrightarrow> R1 isIncludedIn s1)*)
    using SC1 not_overlaps by blast
*)

(*
We can show "R2 \<ge>\<^sub>c\<^sub>i \<^sub>b R1" by its definition.
Since we have obtained "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b" from isHull_def, we can get
"R1 crosses s1 \<or> (R2 isIncludedIn s1 \<longrightarrow> R1 isIncludedIn s1)". 
But we have the assumption that "\<not>(R1 overlaps s1)", so we have that "\<not>(R1 crosses s1)" by
the definition of overlaps.
Thus, we know that in the disjunction above, it must be the case that "(R2 isIncludedIn s1 \<longrightarrow> R1 isIncludedIn s1)".
We have that "R2 isIncludedIn s1" if we assume that "region_to_section R2" gives us s2.
We obtained that "s2 isPartOF s1" from the atLeastAsRestrictiveAs_def "s2 \<le>\<^sub>b s1" (obtained from hull definition)
Therefore, from the intermediate proofs above, we can show that "R2 \<ge>\<^sub>c\<^sub>i \<^sub>b R1"
*)

lemma T6_belongsAsMuchAs: "\<forall>b R1. (\<exists>s. s isHull b \<and> \<not>(R1 overlaps s)) \<longrightarrow> (\<forall>R2. R2 \<ge> \<^sub>b R1)"
proof ((rule allI)+, rule impI, rule allI)
  fix b R1 R2
  assume "\<exists>s. s isHull b \<and> \<not>(R1 overlaps s)"
  then obtain s1 where hull: "s1 isHull b" and not_overlaps: "\<not>(R1 overlaps s1)"
    by blast
  then have section_bundle: "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"
    using isHull_def by blast
  then show "R2 \<ge> \<^sub>b R1"
  proof -
    have overlaps: "\<forall>R3 b R4. \<exists>s. (R3 overlaps s \<or> R3 \<le>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R4) \<and> (s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<or> R3 \<le>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R4)"
      using overlapsAsMuchAs_def by blast
    then show "R2 \<ge> \<^sub>b R1"
      by (meson T1 T6_crosses_isIncludedInAsMuchAs belongsAsMuchAs_def hull isHull_def not_overlaps)
  qed
qed

lemma T7_crosses_isIncludedInAsMuchAs: "\<forall>b R1. (\<exists>s. s isCoreOf b \<and> R1 isIncludedIn s) \<longrightarrow> (\<forall>R2. R1 \<ge>\<^sub>c\<^sub>i \<^sub>b R2)"
proof ((rule allI)+, rule impI, rule allI)
  fix b R1 R2
  fix s2
  assume "\<exists>s. s isCoreOf b \<and> R1 isIncludedIn s"
  then obtain s1 where core: "s1 isCoreOf b" and inclusion1: "R1 isIncludedIn s1"
    by blast
  then have section_bundle1: "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"
    by (simp add: isCore_def)
  then show "R1 \<ge>\<^sub>c\<^sub>i \<^sub>b R2"
    using T2 core crosses_isIncludedInAsMuchAs_def inclusion1 isCore_def by blast
qed

lemma T7_belongsAsMuchAs: "\<forall>b R1. (\<exists>s. s isCoreOf b \<and> R1 isIncludedIn s) \<longrightarrow> (\<forall>R2. R1 \<ge> \<^sub>b R2)"
proof ((rule allI)+, rule impI, rule allI)
  fix b R1 R2
  assume "\<exists>s. s isCoreOf b \<and> R1 isIncludedIn s"
  then obtain s1 where core: "s1 isCoreOf b" and inclusion1: "R1 isIncludedIn s1"
    by blast
  then have section_bundle1: "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"
    by (simp add: isCore_def)
  then show "R1 \<ge> \<^sub>b R2"
  proof -
    have "\<forall>s. R1 overlaps s \<or> \<not> s1 isPartOf s"
      by (meson inclusion1 inclusion_def isPartOf_def overlaps_def section_nonempty)
    then show "R1 \<ge> \<^sub>b R2"
      using T7_crosses_isIncludedInAsMuchAs atLeastAsRestrictiveAs_def belongsAsMuchAs_def core
            inclusion1 isCore_def overlapsAsMuchAs_def by auto
  qed
qed

lemma T8_crosses_isIncludedInAsMuchAs: "\<forall>b R1. (\<exists>s. s isHull b \<and> (R1 crosses s)) \<longrightarrow> (\<forall>R2. R1 \<ge>\<^sub>c\<^sub>i \<^sub>b R2)"
proof ((rule allI)+, rule impI, rule allI)
  fix b R1 R2
  assume "\<exists>s. s isHull b \<and> (R1 crosses s)"
  then obtain s1 where hull: "s1 isHull b" and cross: "R1 crosses s1"
    by blast
  then have section_bundle1: "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"
    using isHull_def by blast
  then show "R1 \<ge>\<^sub>c\<^sub>i \<^sub>b R2"
    using cross crosses_hull crosses_isIncludedInAsMuchAs_def hull by blast
qed

lemma T8_belongsAsMuchAs: "\<forall>b R1. (\<exists>s. s isHull b \<and> (R1 crosses s)) \<longrightarrow> (\<forall>R2. R1 \<ge> \<^sub>b R2)"
proof ((rule allI)+, rule impI, rule allI)
  fix b R1 R2
  assume "\<exists>s. s isHull b \<and> (R1 crosses s)"
  then obtain s1 where hull: "s1 isHull b" and cross: "R1 crosses s1"
    by blast
  then have section_bundle1: "s1 \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b"
    using isHull_def by blast
  then show "R1 \<ge> \<^sub>b R2"
  proof -
    have "\<forall>s. \<not> s \<iota>\<^sub>s\<^sub>e\<^sub>c\<^sub>t\<^sub>i\<^sub>o\<^sub>n b \<or> R1 crosses s"
      using cross crosses_hull hull by blast
    then have overlaps1: "R2 \<le>\<^sub>o\<^sub>v\<^sub>e\<^sub>r\<^sub>l\<^sub>a\<^sub>p\<^sub>s \<^sub>b R1"
      by (simp add: SC1 overlapsAsMuchAs_def)
    then show "R1 \<ge> \<^sub>b R2"
      using T8_crosses_isIncludedInAsMuchAs belongsAsMuchAs_def cross hull by blast
  qed
qed

end

end