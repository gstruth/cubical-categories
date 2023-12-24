(*
Title: Cubical Categories
Authors: Tanguy Massacrier, Georg Struth
Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section\<open>Cubical Categories\<close>

theory CubicalCategories
  imports Catoids.Catoid

begin

text \<open>All categories considered in this theory are single-set categories.\<close>

no_notation src ("\<sigma>")

notation True ("tt") 
notation False ("ff")

abbreviation Fix :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set" where
  "Fix f \<equiv> {x. f x = x}"

text \<open>First we lift locality to powersets.\<close>

lemma (in local_catoid) locality_lifting: "(X \<star> Y \<noteq> {}) = (Tgt X \<inter> Src Y \<noteq> {})"
proof-
  have "(X \<star> Y \<noteq> {}) = (\<exists>x y. x \<in> X \<and> y \<in> Y \<and> x \<odot> y \<noteq> {})"
    by (metis (mono_tags, lifting) all_not_in_conv conv_exp2)
  also have "\<dots> = (\<exists>x y. x \<in> X \<and> y \<in> Y \<and> tgt x = src y)"
    using local.st_local by auto
  also have "\<dots> = (Tgt X \<inter> Src Y \<noteq> {})"
    by blast
  finally show ?thesis.
qed

text \<open>The following lemma about functional catoids is useful in proofs.\<close>

lemma (in functional_catoid) pcomp_def_var4: "\<Delta> x y \<Longrightarrow> x \<odot> y = {x \<otimes> y}"
  using local.pcomp_def_var3 by blast


subsection \<open>Indexed catoids and categories\<close>

class face_map_op = 
  fixes fmap :: "nat \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("\<partial>") 

begin

abbreviation Face :: "nat \<Rightarrow> bool \<Rightarrow> 'a set \<Rightarrow> 'a set" ("\<partial>\<partial>") where
  "\<partial>\<partial> i \<alpha> \<equiv> image (\<partial> i \<alpha>)"

abbreviation face_fix :: "nat \<Rightarrow> 'a set" where
  "face_fix i \<equiv> Fix (\<partial> i ff)"

abbreviation "fFx i x \<equiv> (\<partial> i ff x = x)"

abbreviation "FFx i X \<equiv> (\<forall>x \<in> X. fFx i x)"

end

class icomp_op =
  fixes icomp :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a set" ("_\<odot>\<^bsub>_\<^esub>_"[70,70,70]70)

class imultisemigroup = icomp_op +
  assumes iassoc: "(\<Union>v \<in> y \<odot>\<^bsub>i\<^esub> z. x \<odot>\<^bsub>i\<^esub> v) = (\<Union>v \<in> x \<odot>\<^bsub>i\<^esub> y. v \<odot>\<^bsub>i\<^esub> z)"

begin

sublocale ims: multisemigroup "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y"
  by unfold_locales (simp add: local.iassoc)

abbreviation "DD \<equiv> ims.\<Delta>"

abbreviation iconv :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> 'a set" ("_\<star>\<^bsub>_\<^esub>_"[70,70,70]70) where
  "X \<star>\<^bsub>i\<^esub> Y \<equiv> ims.conv i X Y"

end

class icatoid = imultisemigroup + face_map_op +
  assumes iDst: "DD i x y \<Longrightarrow> \<partial> i tt x = \<partial> i ff y"
  and is_absorb [simp]: "(\<partial> i ff x) \<odot>\<^bsub>i\<^esub> x = {x}"
  and it_absorb [simp]: "x \<odot>\<^bsub>i\<^esub> (\<partial> i tt x) = {x}"

begin

text \<open>Every indexed catoid is a catoid. \<close>

sublocale icid: catoid "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y" "\<partial> i ff" "\<partial> i tt"
  by unfold_locales (simp_all add: iDst)

lemma lFace_Src: "\<partial>\<partial> i ff = icid.Src i"
  by simp

lemma uFace_Tgt: "\<partial>\<partial> i tt = icid.Tgt i"
  by simp

lemma face_fix_sfix: "face_fix = icid.sfix"
  by force

lemma face_fix_tfix: "face_fix = icid.tfix"
  using icid.stopp.stfix_set by presburger

lemma face_fix_prop [simp]: "x \<in> face_fix i = (\<partial> i \<alpha> x = x)"
  by (smt (verit, del_insts) icid.stopp.st_fix mem_Collect_eq)

lemma fFx_prop: "fFx i x = (\<partial> i \<alpha> x = x)"
  by (metis icid.st_eq1 icid.st_eq2)

end

class icategory = icatoid +
  assumes locality: "\<partial> i tt x = \<partial> i ff y \<Longrightarrow> DD i x y"
  and functionality: "z \<in> x \<odot>\<^bsub>i\<^esub> y \<Longrightarrow> z' \<in> x \<odot>\<^bsub>i\<^esub> y \<Longrightarrow> z = z'"

begin 

text \<open>Every indexed category is a (single-set) category.\<close>

sublocale icat: single_set_category "\<lambda>x y. x \<odot>\<^bsub>i\<^esub> y" "\<partial> i ff" "\<partial> i tt"
  apply unfold_locales
    apply (simp add: local.functionality)
   apply (metis dual_order.eq_iff icid.src_local_cond icid.st_locality_locality local.locality)
  by (metis icid.st_locality_locality local.iDst local.locality order_refl)

abbreviation ipcomp :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" ("_\<otimes>\<^bsub>_\<^esub>_"[70,70,70]70) where
  "x \<otimes>\<^bsub>i\<^esub> y \<equiv> icat.pcomp i x y"

lemma (in icategory) iconv_prop: "X \<star>\<^bsub>i\<^esub> Y = {x \<otimes>\<^bsub>i\<^esub>y |x y. x \<in> X \<and> y \<in> Y \<and> DD i x y}"
  by (rule antisym) (clarsimp simp: ims.conv_def, metis local.icat.pcomp_def_var)+

abbreviation "dim_bound k x \<equiv> (\<forall>i. k \<le> i \<longrightarrow> fFx i x)"

abbreviation "fin_dim x \<equiv> (\<exists>k. dim_bound k x)"

end


subsection \<open>Semi-cubical $\omega$-categories\<close>

text \<open>We first define a class for cubical $\omega$-categories without symmetries.\<close>

class semi_cubical_omega_category = icategory +
  assumes face_comm: "i \<noteq> j \<Longrightarrow> \<partial> i \<alpha> \<circ> \<partial> j \<beta> = \<partial> j \<beta> \<circ> \<partial> i \<alpha>"
  and face_func: "i \<noteq> j \<Longrightarrow> DD j x y \<Longrightarrow> \<partial> i \<alpha> (x \<otimes>\<^bsub>j\<^esub> y) = \<partial> i \<alpha> x \<otimes>\<^bsub>j\<^esub> \<partial> i \<alpha> y"
  and interchange: "i \<noteq> j \<Longrightarrow> DD i w x \<Longrightarrow> DD i y z \<Longrightarrow> DD j w y \<Longrightarrow> DD j x z 
                           \<Longrightarrow> (w \<otimes>\<^bsub>i\<^esub> x) \<otimes>\<^bsub>j\<^esub> (y \<otimes>\<^bsub>i\<^esub> z) = (w \<otimes>\<^bsub>j\<^esub> y) \<otimes>\<^bsub>i\<^esub> (x \<otimes>\<^bsub>j\<^esub> z)"
  and fin_fix: "fin_dim x"

begin

lemma fin_fix_var: "\<exists>k. \<forall>i. k < i \<longrightarrow> \<partial> i \<alpha> x = x"
  by (meson less_or_eq_imp_le local.fFx_prop local.fin_fix)

lemma pcomp_face_func_DD: "i \<noteq> j \<Longrightarrow> DD j x y \<Longrightarrow> DD j (\<partial> i \<alpha> x) (\<partial> i \<alpha> y)"
  by (metis comp_apply icat.st_local local.face_comm)

lemma comp_face_func: "i \<noteq> j \<Longrightarrow> (\<partial>\<partial> i \<alpha>) (x \<odot>\<^bsub>j\<^esub> y) \<subseteq> \<partial> i \<alpha> x \<odot>\<^bsub>j\<^esub> \<partial> i \<alpha> y"
  using local.icat.pcomp_def_var local.icat.pcomp_def_var4 local.face_func pcomp_face_func_DD by fastforce

lemma interchange_var: 
  assumes "i \<noteq> j"
  and "(w \<odot>\<^bsub>i\<^esub> x) \<star>\<^bsub>j\<^esub> (y \<odot>\<^bsub>i\<^esub> z) \<noteq> {}"
  and "(w \<odot>\<^bsub>j\<^esub> y) \<star>\<^bsub>i\<^esub> (x \<odot>\<^bsub>j\<^esub> z) \<noteq> {}"
  shows "(w \<odot>\<^bsub>i\<^esub> x) \<star>\<^bsub>j\<^esub> (y \<odot>\<^bsub>i\<^esub> z) = (w \<odot>\<^bsub>j\<^esub> y) \<star>\<^bsub>i\<^esub> (x \<odot>\<^bsub>j\<^esub> z)" 
proof-
  have h1: "DD i w x"
    using assms(2) local.ims.conv_def by force
  have h2: "DD i y z"
    using assms(2) multimagma.conv_distl by force
  have h3: "DD j w y"
    using assms(3) multimagma.conv_def by force
  have h4: "DD j x z"
    using assms(3) local.icid.stopp.conv_def by force
  have "(w \<odot>\<^bsub>i\<^esub> x) \<star>\<^bsub>j\<^esub> (y \<odot>\<^bsub>i\<^esub> z) = {w \<otimes>\<^bsub>i\<^esub> x} \<star>\<^bsub>j\<^esub> {y \<otimes>\<^bsub>i\<^esub> z}"
    using h1 h2 local.icat.pcomp_def_var4 by force
  also have "\<dots> = {(w \<otimes>\<^bsub>i\<^esub> x) \<otimes>\<^bsub>j\<^esub> (y \<otimes>\<^bsub>i\<^esub> z)}"
    using assms(2) calculation local.icat.pcomp_def_var4 by force
  also have "\<dots> = {(w \<otimes>\<^bsub>j\<^esub> y) \<otimes>\<^bsub>i\<^esub> (x \<otimes>\<^bsub>j\<^esub> z)}"
    by (simp add: assms(1) h1 h2 h3 h4 local.interchange)
  also have "\<dots> = {w \<otimes>\<^bsub>j\<^esub> y} \<star>\<^bsub>i\<^esub> {x \<otimes>\<^bsub>j\<^esub> z}"
    by (metis assms(3) h3 h4 local.icat.pcomp_def_var4 multimagma.conv_atom)
  also have "\<dots> = (w \<odot>\<^bsub>j\<^esub> y) \<star>\<^bsub>i\<^esub> (x \<odot>\<^bsub>j\<^esub> z)"
    using h3 h4 local.icat.pcomp_def_var4 by force
  finally show ?thesis.
qed

lemma interchange_var2: 
  assumes "i \<noteq> j"
  and "(\<Union>a \<in> w \<odot>\<^bsub>i\<^esub> x. \<Union>b \<in> y \<odot>\<^bsub>i\<^esub> z. a \<odot>\<^bsub>j\<^esub> b) \<noteq> {}"
  and "(\<Union>c \<in> w \<odot>\<^bsub>j\<^esub> y. \<Union>d \<in> x \<odot>\<^bsub>j\<^esub> z. c \<odot>\<^bsub>i\<^esub> d) \<noteq> {}"
  shows "(\<Union>a \<in> w \<odot>\<^bsub>i\<^esub> x. \<Union>b \<in> y \<odot>\<^bsub>i\<^esub> z. a \<odot>\<^bsub>j\<^esub> b) = (\<Union>c \<in> w \<odot>\<^bsub>j\<^esub> y. \<Union>d \<in> x \<odot>\<^bsub>j\<^esub> z. c \<odot>\<^bsub>i\<^esub> d)"
proof-
  have "{(w \<otimes>\<^bsub>i\<^esub> x) \<otimes>\<^bsub>j\<^esub> (y \<otimes>\<^bsub>i\<^esub> z)} = {(w \<otimes>\<^bsub>j\<^esub> y) \<otimes>\<^bsub>i\<^esub> (x \<otimes>\<^bsub>j\<^esub> z)}"
    using assms(1) assms(2) assms(3) local.interchange by fastforce
  thus ?thesis
    by (metis assms(1) assms(2) assms(3) interchange_var multimagma.conv_def)
qed

lemma face_compat: "\<partial> i \<alpha> \<circ> \<partial> i \<beta>  = \<partial> i \<beta>"
  by (smt (z3) fun.map_ident_strong icid.ts_compat image_iff local.icid.stopp.ts_compat)

lemma face_compat_var [simp]: "\<partial> i \<alpha> (\<partial> i \<beta> x) = \<partial> i \<beta> x"
  by (smt (z3) local.face_fix_prop local.icid.stopp.ST_im local.icid.stopp.tfix_im range_eqI)

lemma face_comm_var: "i \<noteq> j \<Longrightarrow> \<partial> i \<alpha> (\<partial> j \<beta> x) = \<partial> j \<beta> (\<partial> i \<alpha> x)"
  by (meson comp_eq_dest local.face_comm)

lemma face_comm_lift: "i \<noteq> j \<Longrightarrow> \<partial>\<partial> i \<alpha> (\<partial>\<partial> j \<beta> X) = \<partial>\<partial> j \<beta> (\<partial>\<partial> i \<alpha> X)"
  by (simp add: image_comp local.face_comm)

lemma face_func_lift: "i \<noteq> j \<Longrightarrow> (\<partial>\<partial> i \<alpha>) (X \<star>\<^bsub>j\<^esub> Y) \<subseteq> \<partial>\<partial> i \<alpha> X \<star>\<^bsub>j\<^esub> \<partial>\<partial>  i \<alpha> Y"
  using ims.conv_def comp_face_func dual_order.refl image_subset_iff by fastforce

lemma pcomp_lface: "DD i x y \<Longrightarrow> \<partial> i ff (x \<otimes>\<^bsub>i\<^esub> y) = \<partial> i ff x"
  by (simp add: icat.st_local local.icat.sscatml.locall_var)

lemma pcomp_uface: "DD i x y \<Longrightarrow> \<partial> i tt (x \<otimes>\<^bsub>i\<^esub> y) = \<partial> i tt y"
  using icat.st_local local.icat.sscatml.localr_var by force

lemma interchange_DD1:
  assumes "i \<noteq> j"
  and "DD i w x"
  and "DD i y z"
  and "DD j w y"
  and "DD j x z"
  shows "DD j (w \<otimes>\<^bsub>i\<^esub> x) (y \<otimes>\<^bsub>i\<^esub> z)"
proof-
  have a: "\<partial> j tt (w \<otimes>\<^bsub>i\<^esub> x) = \<partial> j tt w \<otimes>\<^bsub>i\<^esub> \<partial> j tt x"
    using assms(1) assms(2) face_func by simp
  also have "\<dots>  = \<partial> j ff y \<otimes>\<^bsub>i\<^esub> \<partial> j ff z"
    using assms(4) assms(5) local.iDst by simp
  also have "\<dots> = \<partial> j ff (y \<otimes>\<^bsub>i\<^esub> z)"
    using assms(1) assms(3) face_func by simp
  finally show ?thesis
    using local.locality by simp
qed

lemma interchange_DD2:
  assumes "i \<noteq> j"
  and "DD i w x"
  and "DD i y z"
  and "DD j w y"
  and "DD j x z"
  shows "DD i (w \<otimes>\<^bsub>j\<^esub> y) (x \<otimes>\<^bsub>j\<^esub> z)"
  using assms interchange_DD1 by simp
                             
lemma face_idem1: "\<partial> i \<alpha> x = \<partial> i \<beta> y \<Longrightarrow> \<partial> i \<alpha> x \<odot>\<^bsub>i\<^esub> \<partial> i \<beta> y = {\<partial> i \<alpha> x}"
  by (metis face_compat_var local.it_absorb)

lemma face_pidem1: "\<partial> i \<alpha> x = \<partial> i \<beta> y \<Longrightarrow> \<partial> i \<alpha> x \<otimes>\<^bsub>i\<^esub> \<partial> i \<beta> y = \<partial> i \<alpha> x"
  by (metis face_compat_var local.icat.sscatml.l0_absorb)

lemma face_pidem2: "\<partial> i \<alpha> x \<noteq> \<partial> i \<beta> y \<Longrightarrow> \<partial> i \<alpha> x \<odot>\<^bsub>i\<^esub> \<partial> i \<beta> y = {}"
  using icat.st_local by force

lemma face_fix_comp_var: "i \<noteq> j \<Longrightarrow> \<partial>\<partial> i \<alpha> (\<partial> i \<alpha> x \<odot>\<^bsub>j\<^esub> \<partial> i \<alpha> y) = \<partial> i \<alpha> x \<odot>\<^bsub>j\<^esub> \<partial> i \<alpha> y"
  by (metis (mono_tags, lifting) comp_face_func empty_is_image face_compat_var local.icat.pcomp_def_var4 subset_singletonD)

lemma interchange_lift_aux: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> DD i x y \<Longrightarrow> x \<otimes>\<^bsub>i\<^esub> y \<in> X \<star>\<^bsub>i\<^esub> Y"
  using local.iconv_prop by fastforce

lemma interchange_lift1:
  assumes "i \<noteq> j"
  and "\<exists>w \<in> W. \<exists>x \<in> X. \<exists>y \<in> Y. \<exists>z \<in> Z. DD i w x \<and> DD i y z \<and> DD j w y \<and> DD j x z"
  shows "((W \<star>\<^bsub>i\<^esub> X) \<star>\<^bsub>j\<^esub> (Y \<star>\<^bsub>i\<^esub> Z)) \<inter> ((W \<star>\<^bsub>j\<^esub> Y) \<star>\<^bsub>i\<^esub> (X \<star>\<^bsub>j\<^esub> Z)) \<noteq> {}"
proof-
  obtain w x y z where h1: "w \<in> W \<and> x \<in> X \<and> y \<in> Y \<and> z \<in> Z \<and> DD i w x \<and> DD i y z \<and> DD j w y \<and> DD j x z"
    using assms(2) by blast
  have h5: "(w \<otimes>\<^bsub>i\<^esub> x) \<otimes>\<^bsub>j\<^esub> (y \<otimes>\<^bsub>i\<^esub> z) \<in> (W \<star>\<^bsub>i\<^esub> X) \<star>\<^bsub>j\<^esub> (Y \<star>\<^bsub>i\<^esub> Z)"
    using assms(1) h1 interchange_lift_aux interchange_DD2 by presburger
  have "(w \<otimes>\<^bsub>j\<^esub> y) \<otimes>\<^bsub>i\<^esub> (x \<otimes>\<^bsub>j\<^esub> z) \<in> (W \<star>\<^bsub>j\<^esub> Y) \<star>\<^bsub>i\<^esub> (X \<star>\<^bsub>j\<^esub> Z)"
    by (simp add: assms(1) h1 interchange_lift_aux interchange_DD2)
  thus ?thesis
    using assms(1) h1 h5 local.interchange by fastforce
qed

lemma interchange_lift2:
  assumes "i \<noteq> j"
  and "\<forall>w \<in> W. \<forall>x \<in> X. \<forall>y \<in> Y. \<forall>z \<in> Z. DD i w x \<and> DD i y z \<and> DD j w y \<and> DD j x z"
  shows "((W \<star>\<^bsub>i\<^esub> X) \<star>\<^bsub>j\<^esub> (Y \<star>\<^bsub>i\<^esub> Z)) = ((W \<star>\<^bsub>j\<^esub> Y) \<star>\<^bsub>i\<^esub> (X \<star>\<^bsub>j\<^esub> Z))"
proof-
  {fix t
  have "(t \<in> (W \<star>\<^bsub>i\<^esub> X) \<star>\<^bsub>j\<^esub> (Y \<star>\<^bsub>i\<^esub> Z)) = (\<exists>w \<in> W. \<exists>x \<in> X. \<exists>y \<in> Y. \<exists>z \<in> Z. DD i w x \<and> DD i y z \<and> DD j (w \<otimes>\<^bsub>i\<^esub> x) (y \<otimes>\<^bsub>i\<^esub> z) \<and> t = (w \<otimes>\<^bsub>i\<^esub> x) \<otimes>\<^bsub>j\<^esub> (y \<otimes>\<^bsub>i\<^esub> z))"
    unfolding iconv_prop by force
  also have "\<dots> = (\<exists>w \<in> W. \<exists>x \<in> X. \<exists>y \<in> Y. \<exists>z \<in> Z. DD i w x \<and> DD i y z \<and> DD j w y \<and> DD j x z \<and> t = (w \<otimes>\<^bsub>i\<^esub> x) \<otimes>\<^bsub>j\<^esub> (y \<otimes>\<^bsub>i\<^esub> z))"
    using assms(1) assms(2) interchange_DD2 by simp
  also have "\<dots> = (\<exists>w \<in> W. \<exists>x \<in> X. \<exists>y \<in> Y. \<exists>z \<in> Z. DD j w y \<and> DD j x z \<and> DD j w y \<and> DD j x z \<and> t = (w \<otimes>\<^bsub>j\<^esub> y) \<otimes>\<^bsub>i\<^esub> (x \<otimes>\<^bsub>j\<^esub> z))"
    by (simp add: assms(1) assms(2) local.interchange)
  also have "\<dots> = (\<exists>w \<in> W. \<exists>x \<in> X. \<exists>y \<in> Y. \<exists>z \<in> Z. DD j w y \<and> DD j x z \<and> DD i (w \<otimes>\<^bsub>j\<^esub> y) (x \<otimes>\<^bsub>j\<^esub> z) \<and> t = (w \<otimes>\<^bsub>j\<^esub> y) \<otimes>\<^bsub>i\<^esub> (x \<otimes>\<^bsub>j\<^esub> z))"
    using assms(1) assms(2) interchange_DD1 by simp
  also have "\<dots> = (t \<in> (W \<star>\<^bsub>j\<^esub> Y) \<star>\<^bsub>i\<^esub> (X \<star>\<^bsub>j\<^esub> Z))"
    unfolding iconv_prop by force
  finally have "(t \<in> (W \<star>\<^bsub>i\<^esub> X) \<star>\<^bsub>j\<^esub> (Y \<star>\<^bsub>i\<^esub> Z)) = (t \<in> (W \<star>\<^bsub>j\<^esub> Y) \<star>\<^bsub>i\<^esub> (X \<star>\<^bsub>j\<^esub> Z))"
    by blast}
  thus ?thesis
    by force
qed

lemma double_fix_prop: "(\<partial> i \<alpha> (\<partial> j \<beta> x) = x) = (fFx i x \<and> fFx j x)"
  by (metis face_comm_var face_compat_var)

end


subsection \<open>Type classes for cubical $\omega$-categories\<close>

abbreviation diffSup :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "diffSup i j k \<equiv> (i - j \<ge> k \<or> j - i \<ge> k)"

class symmetry_ops =
  fixes symmetry :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" ("\<sigma>")
  and inv_symmetry :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" ("\<theta>") 

begin

abbreviation "\<sigma>\<sigma> i \<equiv> image (\<sigma> i)"

abbreviation "\<theta>\<theta> i \<equiv> image (\<theta> i)"

text \<open>symcomp i j composes the symmetry maps from index i to index i+j-1.\<close>

primrec symcomp :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" ("\<Sigma>") where
    "\<Sigma> i 0 x = x"
  | "\<Sigma> i (Suc j) x = \<sigma> (i + j) (\<Sigma> i j x)"

text \<open>inv-symcomp i j composes the inverse symmetries from i+j-1 to i.\<close>

primrec inv_symcomp :: "nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" ("\<Theta>") where
    "\<Theta> i 0 x = x"
  | "\<Theta> i (Suc j) x = \<Theta> i j (\<theta> (i + j) x)"

end

text \<open>Next we define a class for cubical $\omega$-categories.\<close>

class cubical_omega_category = semi_cubical_omega_category + symmetry_ops +
  assumes sym_type: "\<sigma>\<sigma> i (face_fix i) \<subseteq> face_fix (i + 1)"
  and inv_sym_type: "\<theta>\<theta> i (face_fix (i + 1)) \<subseteq> face_fix i"
  and sym_inv_sym: "fFx (i + 1) x \<Longrightarrow> \<sigma> i (\<theta> i x) = x"
  and inv_sym_sym: "fFx i x  \<Longrightarrow> \<theta> i (\<sigma> i x) = x"
  and sym_face1: "fFx i x \<Longrightarrow> \<partial> i \<alpha> (\<sigma> i x) = \<sigma> i (\<partial> (i + 1) \<alpha> x)"
  and sym_face2: "i \<noteq> j \<Longrightarrow> i \<noteq> j + 1 \<Longrightarrow> fFx j x \<Longrightarrow> \<partial> i \<alpha> (\<sigma> j x) = \<sigma> j (\<partial> i \<alpha> x)"
  and sym_func: "i \<noteq> j \<Longrightarrow> fFx i x \<Longrightarrow> fFx i y \<Longrightarrow> DD j x y \<Longrightarrow> 
                     \<sigma> i (x \<otimes>\<^bsub>j\<^esub> y) = (if j = i + 1 then \<sigma> i x \<otimes>\<^bsub>i\<^esub> \<sigma> i y else \<sigma> i x \<otimes>\<^bsub>j\<^esub> \<sigma> i y)"
  and sym_fix: "fFx i x \<Longrightarrow> fFx (i + 1) x \<Longrightarrow> \<sigma> i x = x"
  and sym_sym_braid: "diffSup i j 2 \<Longrightarrow> fFx i x \<Longrightarrow> fFx j x  \<Longrightarrow> \<sigma> i (\<sigma> j x) = \<sigma> j (\<sigma> i x)"

begin

text \<open>First we prove variants of the axioms.\<close>

lemma sym_type_var: "fFx i x \<Longrightarrow> fFx (i + 1) (\<sigma> i x)"
  by (meson image_subset_iff local.face_fix_prop local.sym_type)

lemma sym_type_var1 [simp]: "\<partial> (i + 1) \<alpha> (\<sigma> i (\<partial> i \<alpha> x)) = \<sigma> i (\<partial> i \<alpha> x)"
  by (metis local.face_compat_var sym_type_var)

lemma sym_type_var2 [simp]: "\<partial> (i + 1) \<alpha> \<circ> \<sigma> i \<circ> \<partial> i \<alpha> = \<sigma> i \<circ> \<partial> i \<alpha>"
  unfolding comp_def fun_eq_iff using sym_type_var1 by simp

lemma sym_type_var_lift_var [simp]: "\<partial>\<partial> (i + 1) \<alpha> (\<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X)) = \<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X)"
  by (metis image_comp sym_type_var2)

lemma sym_type_var_lift [simp]: 
  assumes "FFx i X"
  shows "\<partial>\<partial> (i + 1) \<alpha> (\<sigma>\<sigma> i X) = \<sigma>\<sigma> i X"
proof-
  have "\<partial>\<partial> (i + 1) \<alpha> (\<sigma>\<sigma> i X) = {\<partial> (i + 1) \<alpha> (\<sigma> i x) |x. x \<in> X}"
    by blast
  also have "\<dots>  = {\<sigma> i x |x. x \<in> X}"
    by (metis assms local.fFx_prop sym_type_var)
  also have "\<dots> = \<sigma>\<sigma> i X"
    by (simp add: setcompr_eq_image)
  finally show ?thesis.
qed

lemma inv_sym_type_var: "fFx (i + 1) x \<Longrightarrow> fFx i (\<theta> i x)"
  by (meson image_subset_iff local.face_fix_prop local.inv_sym_type)

lemma inv_sym_type_var1 [simp]: "\<partial> i \<alpha> (\<theta> i (\<partial> (i + 1) \<alpha> x)) = \<theta> i (\<partial> (i + 1) \<alpha> x)"
  by (metis inv_sym_type_var local.face_compat_var)

lemma inv_sym_type_var2 [simp]: "\<partial> i \<alpha> \<circ> \<theta> i \<circ> \<partial> (i + 1) \<alpha> = \<theta> i \<circ> \<partial> (i + 1) \<alpha>"
  unfolding comp_def fun_eq_iff using inv_sym_type_var1 by simp

lemma inv_sym_type_lift_var [simp]: "\<partial>\<partial> i \<alpha> (\<theta>\<theta> i (\<partial>\<partial> (i + 1) \<alpha> X)) = \<theta>\<theta> i (\<partial>\<partial> (i + 1) \<alpha> X)"
  by (metis image_comp inv_sym_type_var2)

lemma inv_sym_type_lift: 
  assumes "FFx (i + 1) X"
  shows "\<partial>\<partial> i \<alpha> (\<theta>\<theta> i X) = \<theta>\<theta> i X"
  by (smt (z3) assms icid.st_eq1 image_cong image_image inv_sym_type_var)

lemma sym_inv_sym_var1 [simp]: "\<sigma> i (\<theta> i (\<partial> (i + 1) \<alpha> x)) = \<partial> (i + 1) \<alpha> x"
  by (simp add: local.sym_inv_sym)

lemma sym_inv_sym_var2 [simp]: "\<sigma> i \<circ> \<theta> i \<circ> \<partial> (i + 1) \<alpha> = \<partial> (i + 1) \<alpha>"
  unfolding comp_def fun_eq_iff using sym_inv_sym_var1 by simp

lemma sym_inv_sym_lift_var: "\<sigma>\<sigma> i (\<theta>\<theta> i (\<partial>\<partial> (i + 1) \<alpha> X)) = \<partial>\<partial> (i + 1) \<alpha> X"
  by (metis image_comp sym_inv_sym_var2)

lemma sym_inv_sym_lift: 
  assumes "FFx (i + 1) X"
  shows "\<sigma>\<sigma> i (\<theta>\<theta> i X) = X"
proof-
  have "\<sigma>\<sigma> i (\<theta>\<theta> i X) = {\<sigma> i (\<theta> i x) |x. x \<in> X}"
    by blast
  thus ?thesis
    using assms local.sym_inv_sym by force
qed

lemma inv_sym_sym_var1 [simp]: "\<theta> i (\<sigma> i (\<partial> i \<alpha> x)) = \<partial> i \<alpha> x"
  by (simp add: local.inv_sym_sym)

lemma inv_sym_sym_var2 [simp]: "\<theta> i \<circ> \<sigma> i \<circ> \<partial> i \<alpha> = \<partial> i \<alpha>"
  unfolding comp_def fun_eq_iff by simp

lemma inv_sym_sym_lift_var [simp]: "\<theta>\<theta> i (\<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X)) = \<partial>\<partial> i \<alpha> X"
  by (simp add: image_comp)

lemma inv_sym_sym_lift: 
  assumes "FFx i X"
  shows "\<theta>\<theta> i (\<sigma>\<sigma> i X) = X"
  by (metis assms image_cong image_ident inv_sym_sym_lift_var)

lemma sym_fix_var1 [simp]: "\<sigma> i (\<partial> i \<alpha> (\<partial> (i + 1) \<beta> x)) = \<partial> i \<alpha> (\<partial> (i + 1) \<beta> x)"
  by (simp add: local.face_comm_var local.sym_fix)

lemma sym_fix_var2 [simp]: "\<sigma> i \<circ> \<partial> i \<alpha> \<circ> \<partial> (i + 1) \<beta> = \<partial> i \<alpha> \<circ> \<partial> (i + 1) \<beta>"
  unfolding comp_def fun_eq_iff using sym_fix_var1 by simp

lemma sym_fix_lift_var: "\<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> (\<partial>\<partial> (i + 1) \<beta> X)) = \<partial>\<partial> i \<alpha> (\<partial>\<partial> (i + 1) \<beta> X)"
  by (metis image_comp sym_fix_var2)

lemma sym_fix_lift: 
  assumes "FFx i X"
  and "FFx (i + 1) X"
  shows "\<sigma>\<sigma> i X = X"
  using assms local.sym_fix by simp

lemma sym_face1_var1: "\<partial> i \<alpha> (\<sigma> i (\<partial> i \<beta> x)) = \<sigma> i (\<partial> (i + 1) \<alpha> (\<partial> i \<beta> x))"
  by (simp add: local.sym_face1)

lemma sym_face1_var2: "\<partial> i \<alpha> \<circ> \<sigma> i \<circ> \<partial> i \<beta>  = \<sigma> i \<circ> \<partial> (i + 1) \<alpha> \<circ> \<partial> i \<beta>"
  by (simp add: comp_def local.sym_face1)

lemma sym_face1_lift_var: "\<partial>\<partial> i \<alpha> (\<sigma>\<sigma> i (\<partial>\<partial> i \<beta> X)) = \<sigma>\<sigma> i (\<partial>\<partial> (i + 1) \<alpha> (\<partial>\<partial> i \<beta> X))"
  by (metis image_comp sym_face1_var2)

lemma sym_face1_lift: 
  assumes "FFx i X"
  shows "\<partial>\<partial> i \<alpha> (\<sigma>\<sigma> i X) = \<sigma>\<sigma> i (\<partial>\<partial> (i + 1) \<alpha> X)"
  by (smt (z3) assms image_cong image_image local.sym_face1)

lemma sym_face2_var1: 
  assumes "i \<noteq> j"
  and "i \<noteq> j + 1"
  shows "\<partial> i \<alpha> (\<sigma> j (\<partial> j \<beta> x)) = \<sigma> j (\<partial> i \<alpha> (\<partial> j \<beta> x))"
  using assms local.sym_face2 by simp

lemma sym_face2_var2: 
  assumes "i \<noteq> j"
  and "i \<noteq> j + 1"
  shows  "\<partial> i \<alpha> \<circ> \<sigma> j \<circ> \<partial> j \<beta> = \<sigma> j \<circ> \<partial> i \<alpha> \<circ> \<partial> j \<beta>"
  unfolding comp_def fun_eq_iff using assms sym_face2_var1 by simp

lemma sym_face2_lift_var: 
  assumes "i \<noteq> j"
  and "i \<noteq> j + 1"
  shows "\<partial>\<partial> i \<alpha> (\<sigma>\<sigma> j (\<partial>\<partial> j \<beta> X)) = \<sigma>\<sigma> j (\<partial>\<partial> i \<alpha> (\<partial>\<partial> j \<beta> X))"
  by (metis assms image_comp sym_face2_var2)

lemma sym_face2_lift: 
  assumes "i \<noteq> j"
  and "i \<noteq> j + 1"
  and "FFx j X"
  shows "\<partial>\<partial> i \<alpha> (\<sigma>\<sigma> j X) = \<sigma>\<sigma> j (\<partial>\<partial> i \<alpha> X)"
  by (smt (z3) assms image_cong image_image sym_face2_var1)

lemma sym_sym_braid_var1: 
  assumes "diffSup i j 2"
  shows "\<sigma> i (\<sigma> j (\<partial> i \<alpha> (\<partial> j \<beta> x))) = \<sigma> j (\<sigma> i (\<partial> i \<alpha> (\<partial> j \<beta> x)))"
  using assms local.face_comm_var local.sym_sym_braid by force

lemma sym_sym_braid_var2: 
  assumes "diffSup i j 2"
  shows "\<sigma> i \<circ> \<sigma> j \<circ> \<partial> i \<alpha> \<circ> \<partial> j \<beta> = \<sigma> j \<circ> \<sigma> i \<circ> \<partial> i \<alpha> \<circ> \<partial> j \<beta>"
  using assms sym_sym_braid_var1 by fastforce

lemma sym_sym_braid_lift_var: 
  assumes "diffSup i j 2"
  shows "\<sigma>\<sigma> i (\<sigma>\<sigma> j (\<partial>\<partial> i \<alpha> (\<partial>\<partial> j \<beta> X))) = \<sigma>\<sigma> j (\<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> (\<partial>\<partial> j \<beta> X)))"
proof-
  have "\<sigma>\<sigma> i (\<sigma>\<sigma> j (\<partial>\<partial> i \<alpha> (\<partial>\<partial> j \<beta> X))) = {\<sigma> i (\<sigma> j (\<partial> i \<alpha> (\<partial> j \<beta> x))) |x. x \<in> X}"
    by blast
  also have "\<dots> = {\<sigma> j (\<sigma> i (\<partial> i \<alpha> (\<partial> j \<beta> x))) |x. x \<in> X}"
    by (metis (full_types, opaque_lifting) assms sym_sym_braid_var1)
  finally show ?thesis
    by (simp add: Setcompr_eq_image image_image)
qed

lemma sym_sym_braid_lift: 
  assumes "diffSup i j 2"
  and "FFx i X"
  and "FFx j X"
  shows "\<sigma>\<sigma> i (\<sigma>\<sigma> j X) = \<sigma>\<sigma> j (\<sigma>\<sigma> i X)"
  by (smt (z3) assms comp_apply image_comp image_cong sym_sym_braid_var1)

lemma sym_func2: 
  assumes "fFx i x" 
  and "fFx i y" 
  and "DD (i + 1) x y"
  shows "\<sigma> i (x \<otimes>\<^bsub>(i + 1)\<^esub> y) = \<sigma> i x \<otimes>\<^bsub>i\<^esub> \<sigma> i y"
  using assms local.sym_func by simp

lemma sym_func3: 
  assumes "i \<noteq> j"
  and "j \<noteq> i + 1"
  and "fFx i x"
  and "fFx i y"
  and "DD j x y" 
  shows "\<sigma> i (x \<otimes>\<^bsub>j\<^esub> y) = \<sigma> i x \<otimes>\<^bsub>j\<^esub> \<sigma> i y"
  using assms local.sym_func by simp

lemma sym_func2_var1:
  assumes "DD (i + 1) (\<partial> i \<alpha> x) (\<partial> i \<beta> y)"
  shows "\<sigma> i (\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = \<sigma> i (\<partial> i \<alpha> x) \<otimes>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y)"
  using assms local.face_compat_var local.sym_func2 by simp

lemma sym_func3_var1: 
  assumes "i \<noteq> j" 
  and "j \<noteq> i + 1"
  and "DD j (\<partial> i \<alpha> x) (\<partial> i \<beta> y)" 
  shows "\<sigma> i (\<partial> i \<alpha> x \<otimes>\<^bsub>j\<^esub> \<partial> i \<beta> y) = \<sigma> i (\<partial> i \<alpha> x) \<otimes>\<^bsub>j\<^esub> \<sigma> i (\<partial> i \<beta> y)"
  using assms local.face_compat_var local.sym_func3 by simp

lemma sym_func2_DD: 
  assumes "fFx i x"
  and "fFx i y" 
  shows "DD (i + 1) x y = DD i (\<sigma> i x) (\<sigma> i y)"
  by (metis assms icat.st_local local.face_comm_var local.sym_face1 sym_fix_var1)

lemma func2_var2: "\<sigma>\<sigma> i (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = \<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y)"
proof (cases "DD (i + 1) (\<partial> i \<alpha> x) (\<partial> i \<beta> y)")
  case True
  have "\<sigma>\<sigma> i (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = \<sigma>\<sigma> i {\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y}"
    using True local.icat.pcomp_def_var4 by simp
  also have "\<dots> = {\<sigma> i (\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y)}"
    by simp
  also have "\<dots> = {\<sigma> i (\<partial> i \<alpha> x) \<otimes>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y)}"
    using True sym_func2_var1 by simp
  also have "\<dots> = \<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y)"
    using True local.icat.pcomp_def_var4 sym_func2_DD by simp
  finally show ?thesis.
next
  case False
  thus ?thesis
    using local.sym_func2_DD by simp
qed

lemma sym_func2_lift_var1: "\<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X \<star>\<^bsub>(i + 1)\<^esub> \<partial>\<partial> i \<beta> Y) = \<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X) \<star>\<^bsub>i\<^esub> \<sigma>\<sigma> i (\<partial>\<partial> i \<beta> Y)"
proof-
  have "\<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X \<star>\<^bsub>(i + 1)\<^esub> \<partial>\<partial> i \<beta> Y) = \<sigma>\<sigma> i {x \<otimes>\<^bsub>(i + 1)\<^esub> y |x y. x \<in> \<partial>\<partial> i \<alpha> X \<and> y \<in> \<partial>\<partial> i \<beta> Y \<and> DD (i + 1) x y}"
    using local.iconv_prop by presburger
  also have "\<dots> = {\<sigma> i (\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) |x y. x \<in> X \<and> y \<in> Y \<and> DD (i + 1) (\<partial> i \<alpha> x) (\<partial> i \<beta> y)}"
    by blast
  also have "\<dots> = {\<sigma> i (\<partial> i \<alpha> x) \<otimes>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y) |x y. x \<in> X \<and> y \<in> Y \<and> DD i (\<sigma> i (\<partial> i \<alpha> x)) (\<sigma> i (\<partial> i \<beta> y))}"
    using func2_var2 sym_func2_var1 by fastforce
  also have "\<dots> = {x \<otimes>\<^bsub>i\<^esub> y |x y. x \<in> \<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X) \<and> y \<in> \<sigma>\<sigma> i (\<partial>\<partial> i \<beta> Y) \<and> DD i x y}"
    by blast
  also have "\<dots> = \<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X) \<star>\<^bsub>i\<^esub> \<sigma>\<sigma> i (\<partial>\<partial> i \<beta> Y)"
    using local.iconv_prop by presburger
  finally show ?thesis.
qed

lemma sym_func2_lift: 
  assumes "FFx i X"
  and "FFx i Y"
  shows "\<sigma>\<sigma> i (X \<star>\<^bsub>(i + 1)\<^esub> Y) = \<sigma>\<sigma> i X \<star>\<^bsub>i\<^esub> \<sigma>\<sigma> i Y"
proof-
  have "\<sigma>\<sigma> i (X \<star>\<^bsub>(i + 1)\<^esub> Y) = \<sigma>\<sigma> i (\<partial>\<partial> i tt X \<star>\<^bsub>(i + 1)\<^esub> \<partial>\<partial> i tt Y)"
    by (smt (verit) assms image_cong image_ident local.icid.stopp.ST_compat)
  also have "\<dots> = \<sigma>\<sigma> i (\<partial>\<partial> i tt X) \<star>\<^bsub>i\<^esub> \<sigma>\<sigma> i (\<partial>\<partial> i tt Y)"
    using sym_func2_lift_var1 by simp
  also have "\<dots> = \<sigma>\<sigma> i X \<star>\<^bsub>i\<^esub> \<sigma>\<sigma> i Y"
    using assms icid.st_eq1 by simp
  finally show ?thesis.
qed

lemma func3_var1: 
  assumes "i \<noteq> j"
  and "j \<noteq> i + 1" 
  shows "\<sigma>\<sigma> i (\<partial> i \<alpha> x \<odot>\<^bsub>j\<^esub> \<partial> i \<beta> y) = \<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>j\<^esub> \<sigma> i (\<partial> i \<beta> y)"
proof (cases "DD j (\<partial> i \<alpha> x) (\<partial> i \<beta> y)")
  case True
  have "\<sigma>\<sigma> i (\<partial> i \<alpha> x \<odot>\<^bsub>j\<^esub> \<partial> i \<beta> y) = \<sigma>\<sigma> i {\<partial> i \<alpha> x \<otimes>\<^bsub>j\<^esub> \<partial> i \<beta> y}"
    using True local.icat.pcomp_def_var4 by simp
  also have "\<dots> = {\<sigma> i (\<partial> i \<alpha> x \<otimes>\<^bsub>j\<^esub> \<partial> i \<beta> y)}"
    by simp
  also have "\<dots> = {\<sigma> i (\<partial> i \<alpha> x) \<otimes>\<^bsub>j\<^esub> \<sigma> i (\<partial> i \<beta> y)}"
    using True assms sym_func3_var1 by simp
  also have "\<dots> = \<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>j\<^esub> \<sigma> i (\<partial> i \<beta> y)"
    using True assms icat.st_local local.icat.pcomp_def_var4 sym_face2_var1 by simp
  finally show ?thesis.
next
  case False
  thus ?thesis
    by (metis assms empty_is_image icat.st_local inv_sym_sym_var1 local.face_comm_var sym_face2_var1)
qed

lemma sym_func3_lift_var1: 
  assumes "i \<noteq> j"
  and "j \<noteq> i + 1" 
  shows "\<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X \<star>\<^bsub>j\<^esub> \<partial>\<partial> i \<beta> Y) = \<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X) \<star>\<^bsub>j\<^esub> \<sigma>\<sigma> i (\<partial>\<partial> i \<beta> Y)"
proof-
  have a: "\<forall>x \<in> X. \<forall>y \<in> Y.  DD j (\<partial> i \<alpha> x) (\<partial> i \<beta> y) \<longrightarrow> DD j (\<sigma> i (\<partial> i \<alpha> x)) (\<sigma> i (\<partial> i \<beta> y))"
    by (metis assms local.iDst local.locality sym_face2_var1)
  have "\<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X \<star>\<^bsub>j\<^esub> \<partial>\<partial> i \<beta> Y) = \<sigma>\<sigma> i {x \<otimes>\<^bsub>j\<^esub> y |x y. x \<in> \<partial>\<partial> i \<alpha> X \<and> y \<in> \<partial>\<partial> i \<beta> Y \<and> DD j x y}"
    using local.iconv_prop by presburger
  also have "\<dots> = {\<sigma> i (\<partial> i \<alpha> x \<otimes>\<^bsub>j\<^esub> \<partial> i \<beta> y) |x y. x \<in> X \<and> y \<in> Y \<and> DD j (\<partial> i \<alpha> x) (\<partial> i \<beta> y)}"
    by force
  also have "\<dots> = {\<sigma> i (\<partial> i \<alpha> x) \<otimes>\<^bsub>j\<^esub> \<sigma> i (\<partial> i \<beta> y) |x y. x \<in> X \<and> y \<in> Y \<and> DD j (\<sigma> i (\<partial> i \<alpha> x)) (\<sigma> i (\<partial> i \<beta> y))}"
    using assms func3_var1 sym_func3_var1 by fastforce
  also have "\<dots> = {x \<otimes>\<^bsub>j\<^esub> y |x y. x \<in> \<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X) \<and> y \<in> \<sigma>\<sigma> i (\<partial>\<partial> i \<beta> Y) \<and> DD j x y}"
    by force
  also have "\<dots> = \<sigma>\<sigma> i (\<partial>\<partial> i \<alpha> X) \<star>\<^bsub>j\<^esub> \<sigma>\<sigma> i (\<partial>\<partial> i \<beta> Y)"
    using local.iconv_prop by presburger
  finally show ?thesis.
qed

lemma sym_func3_lift: 
  assumes "i \<noteq> j"
  and "j \<noteq> i + 1"
  and "FFx i X"
  and "FFx i Y"
  shows "\<sigma>\<sigma> i (X \<star>\<^bsub>j\<^esub> Y) = \<sigma>\<sigma> i X \<star>\<^bsub>j\<^esub> \<sigma>\<sigma> i Y"
proof-
  have "\<sigma>\<sigma> i (X \<star>\<^bsub>j\<^esub> Y) = \<sigma>\<sigma> i (\<partial>\<partial> i tt X \<star>\<^bsub>j\<^esub> \<partial>\<partial> i tt Y)"
    by (smt (verit) assms(3) assms(4) image_cong image_ident local.icid.stopp.ST_compat)
  also have "\<dots> = \<sigma>\<sigma> i (\<partial>\<partial> i tt X) \<star>\<^bsub>j\<^esub> \<sigma>\<sigma> i (\<partial>\<partial> i tt Y)"
    using assms(1) assms(2) sym_func3_lift_var1 by presburger
  also have "\<dots> = \<sigma>\<sigma> i X \<star>\<^bsub>j\<^esub> \<sigma>\<sigma> i Y"
    using assms(3) assms(4) icid.st_eq1 by simp
  finally show ?thesis.
qed

lemma sym_func3_var2: "i \<noteq> j \<Longrightarrow> \<sigma>\<sigma> i (\<partial> i \<alpha> x \<odot>\<^bsub>j\<^esub> \<partial> i \<beta> y) = (if j = i + 1 then \<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y) else \<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>j\<^esub> \<sigma> i (\<partial> i \<beta> y))"
  using func2_var2 func3_var1 by simp

text \<open>Symmetries and inverse symmetries form a bijective pair on suitable fixpoints of the face maps.\<close>

lemma sym_inj: "inj_on (\<sigma> i) (face_fix i)"
  by (smt (verit, del_insts) CollectD inj_onI local.inv_sym_sym)

lemma sym_inj_var: 
  assumes "fFx i x"
  and "fFx i y"
  and "\<sigma> i x = \<sigma> i y"
  shows "x = y"
  by (metis assms inv_sym_sym_var1)

lemma inv_sym_inj: "inj_on (\<theta> i) (face_fix (i + 1))"
  by (smt (verit, del_insts) CollectD inj_onI local.sym_inv_sym)

lemma inv_sym_inj_var: 
  assumes "fFx (i + 1) x"
  and "fFx (i + 1) y"
  and "\<theta> i x = \<theta> i y"
  shows "x = y"
  by (metis assms local.sym_inv_sym)

lemma surj_sym: "image (\<sigma> i) (face_fix i) = face_fix (i + 1)"
  by (safe, metis sym_type_var1, smt (verit, del_insts) imageI inv_sym_type_var1 mem_Collect_eq sym_inv_sym_var1)

lemma surj_inv_sym: "image (\<theta> i) (face_fix (i + 1)) = face_fix i"
  by (safe, metis inv_sym_type_var1, smt (verit, del_insts) imageI inv_sym_sym_var1 mem_Collect_eq sym_type_var1)

lemma sym_adj: 
  assumes "fFx i x"
  and "fFx (i + 1) y "
  shows "(\<sigma> i x = y) = (x = \<theta> i y)"
  using assms local.inv_sym_sym local.sym_inv_sym by force

text \<open>Next we list properties for inverse symmetries corresponding to the axioms.\<close>

lemma inv_sym: 
  assumes "fFx i x"
  and "fFx (i + 1) x"
  shows "\<theta> i x = x"
proof-
  have "x = \<sigma> i x"
    using assms local.sym_fix by simp
  thus ?thesis
    using assms sym_adj by force
qed

lemma inv_sym_face2:
  assumes "i \<noteq> j"
  and "i \<noteq> j + 1"
  and "fFx (j + 1) x"
  shows "\<partial> i \<alpha> (\<theta> j x) = \<theta> j (\<partial> i \<alpha> x)"
proof-
  have "\<sigma> j (\<partial> i \<alpha> (\<theta> j x)) = \<sigma> j (\<partial> i \<alpha> (\<partial> j ff (\<theta> j x)))"
    using assms(3) inv_sym_type_var by simp
  also have "\<dots> = \<partial> i \<alpha> (\<sigma> j (\<partial> j \<alpha> (\<theta> j x)))"
    by (metis assms inv_sym_type_var local.fFx_prop sym_face2_var1)
  also have "\<dots> = \<partial> i \<alpha> (\<sigma> j (\<theta> j x))"
    using assms calculation inv_sym_type_var local.sym_face2 by presburger
  also have "\<dots> = \<partial> i \<alpha> (\<partial> (j + 1) \<alpha> x)"
    by (metis assms(3) local.face_compat_var sym_inv_sym_var1)
  finally have "\<sigma> j (\<partial> i \<alpha> (\<theta> j x)) = \<partial> i \<alpha> (\<partial> (j + 1) \<alpha> x)".
  thus ?thesis
    by (metis assms(3) inv_sym_type_var local.fFx_prop local.face_comm_var local.inv_sym_sym)
qed

lemma sym_braid: 
  assumes "fFx i x"
  and "fFx (i + 1) x"
  shows "\<sigma> i (\<sigma> (i + 1) (\<sigma> i x)) = \<sigma> (i + 1) (\<sigma> i (\<sigma> (i + 1) x))"
  using assms local.sym_face2 local.sym_fix sym_type_var by simp

lemma inv_sym_braid:
  assumes "fFx (i + 1) x"
  and "fFx (i + 2) x"
  shows "\<theta> i (\<theta> (i + 1) (\<theta> i x)) = \<theta> (i + 1) (\<theta> i (\<theta> (i + 1) x))"
  using assms inv_sym inv_sym_face2 inv_sym_type_var by simp

lemma sym_inv_sym_braid: 
  assumes "diffSup i j 2" 
  and "fFx (j + 1) x"
  and "fFx i x"
  shows "\<sigma> i (\<theta> j x) = \<theta> j (\<sigma> i x)"
  by (smt (z3) add_diff_cancel_left' assms diff_is_0_eq inv_sym_face2 inv_sym_sym_var1 inv_sym_type_var le_add1 local.sym_face2 one_add_one rel_simps(28) sym_inv_sym_var1 sym_sym_braid_var1)

lemma sym_func1: 
  assumes "fFx i x"
  and "fFx i y"
  and "DD i x y"
  shows "\<sigma> i (x \<otimes>\<^bsub>i\<^esub> y) = \<sigma> i x \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i y"
  by (metis assms icid.ts_compat local.iDst local.icat.sscatml.l0_absorb sym_type_var1)

lemma sym_func1_var1: "\<sigma>\<sigma> i (\<partial> i \<alpha> x \<odot>\<^bsub>i\<^esub> \<partial> i \<beta> y) = \<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<sigma> i (\<partial> i \<beta> y)"
  by (metis icid.t_idem image_empty image_insert inv_sym_sym_var1 local.face_compat_var local.icid.stopp.Dst sym_type_var1)

lemma inv_sym_func2_var1: "\<theta>\<theta> i (\<partial> (i + 1) \<alpha> x \<odot>\<^bsub>i\<^esub> \<partial> (i + 1) \<beta> y) = \<theta> i (\<partial> (i + 1) \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<theta> i (\<partial> (i + 1) \<beta> y)"
proof-
  have "\<sigma>\<sigma> i (\<theta> i (\<partial> (i + 1) \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<theta> i (\<partial> (i + 1) \<beta> y)) = \<partial> (i + 1) \<alpha> x \<odot>\<^bsub>i\<^esub> \<partial> (i + 1) \<beta> y"
    by (metis func2_var2 inv_sym_type_var1 sym_inv_sym_var1)
  hence "\<sigma>\<sigma> i (\<partial>\<partial> i ff (\<theta> i (\<partial> (i + 1) \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<theta> i (\<partial> (i + 1) \<beta> y))) = \<partial>\<partial> (i + 1) ff (\<partial> (i + 1) \<alpha> x \<odot>\<^bsub>i\<^esub> \<partial> (i + 1) \<beta> y)"
    by (smt (z3) empty_is_image image_insert inv_sym_type_var local.face_compat_var local.face_fix_comp_var local.iDst local.it_absorb)
  hence "\<partial>\<partial> i ff (\<theta> i (\<partial> (i + 1) \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<theta> i (\<partial> (i + 1) \<beta> y)) = \<theta>\<theta> i (\<partial>\<partial> (i + 1) ff (\<partial> (i + 1) \<alpha> x \<odot>\<^bsub>i\<^esub> \<partial> (i + 1) \<beta> y))"
    by (smt (z3) image_empty image_insert local.icat.functionality_lem_var local.inv_sym_sym_var1)
  thus ?thesis
    by (metis add_cancel_right_right dual_order.eq_iff inv_sym_type_var1 local.face_compat_var local.face_fix_comp_var not_one_le_zero)
qed

lemma inv_sym_func3_var1: "\<theta>\<theta> i ((\<partial> (i + 1) \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> (\<partial> (i + 1) \<beta> y)) = \<theta> i (\<partial> (i + 1) \<alpha> x) \<odot>\<^bsub>i\<^esub> \<theta> i (\<partial> (i + 1) \<beta> y)"
  by (smt (z3) empty_is_image image_insert inv_sym_type_var1 local.face_idem1 local.face_pidem2 sym_inv_sym_var1)

lemma inv_sym_func_var1: 
  assumes "i \<noteq> j"
  and "j \<noteq> i + 1"
  shows "\<theta>\<theta> i ((\<partial> (i + 1) \<alpha> x) \<odot>\<^bsub>j\<^esub> (\<partial> (i + 1) \<beta> y)) = \<theta> i (\<partial> (i + 1) \<alpha> x) \<odot>\<^bsub>j\<^esub> \<theta> i (\<partial> (i + 1) \<beta> y)"
proof-
  have "\<sigma>\<sigma> i ((\<theta> i (\<partial> (i + 1) \<alpha> x)) \<odot>\<^bsub>j\<^esub> (\<theta> i (\<partial> (i + 1) \<beta> y))) = \<partial> (i + 1) \<alpha> x \<odot>\<^bsub>j\<^esub> \<partial> (i + 1) \<beta> y"
    by (metis assms func3_var1 inv_sym_type_var1 sym_inv_sym_var1)
  thus ?thesis
    by (smt (z3) assms(1) icid.st_eq2 inv_sym_sym_lift inv_sym_type_var1 local.icat.pcomp_def_var local.face_func)
qed

lemma inv_sym_func2:
  assumes "fFx (i + 1) x"
  and "fFx (i + 1) y"
  and "DD i x y"
  shows "\<theta> i (x \<otimes>\<^bsub>i\<^esub> y) = \<theta> i x \<otimes>\<^bsub>(i + 1)\<^esub> \<theta> i y"
proof-
  have "{\<theta> i (x \<otimes>\<^bsub>i\<^esub> y)} = \<theta>\<theta> i (x \<odot>\<^bsub>i\<^esub> y)"
    using assms(3) local.icat.pcomp_def_var4 by fastforce
  also have "\<dots> = \<theta> i x \<odot>\<^bsub>(i + 1)\<^esub> \<theta> i y"
    by (metis assms(1) assms(2) inv_sym_func2_var1)
  also have "\<dots> = {\<theta> i x \<otimes>\<^bsub>(i + 1)\<^esub> \<theta> i y}"
    by (metis calculation insert_not_empty local.icat.pcomp_def_var4)
  finally show ?thesis
    by simp
qed

lemma inv_sym_func3: 
  assumes "fFx (i + 1) x"
  and "fFx (i + 1) y"
  and "DD (i + 1) x y"
  shows "\<theta> i (x \<otimes>\<^bsub>(i + 1)\<^esub> y) = \<theta> i x \<otimes>\<^bsub>i\<^esub> \<theta> i y"
  by (metis assms icat.st_local icid.st_fix inv_sym_type_var1 local.icat.sscatml.l0_absorb)

lemma inv_sym_func: 
  assumes "i \<noteq> j"
  and "j \<noteq> i + 1"
  and "fFx (i + 1) x"
  and "fFx (i + 1) y"
  and "DD j x y"
  shows "\<theta> i (x \<otimes>\<^bsub>j\<^esub> y) = \<theta> i x \<otimes>\<^bsub>j\<^esub> \<theta> i y"
proof-
  have "{\<theta> i (x \<otimes>\<^bsub>j\<^esub> y)} = \<theta>\<theta> i (x \<odot>\<^bsub>j\<^esub> y)"
    using assms(5) local.icat.pcomp_def_var4 by fastforce
  also have "\<dots> = \<theta> i x \<odot>\<^bsub>j\<^esub> \<theta> i y"
    by (metis assms(1) assms(2) assms(3) assms(4) inv_sym_func_var1)
  also have "\<dots> =  {\<theta> i x \<otimes>\<^bsub>j\<^esub> \<theta> i y}"
    by (metis calculation insert_not_empty local.icat.pcomp_def_var4)
  finally show ?thesis
    by simp
qed

text \<open>The following properties are related to faces and braids.\<close>

lemma sym_face3:
  assumes "fFx i x"
  shows "\<partial> (i + 1) \<alpha> (\<sigma> i x) = \<sigma> i (\<partial> i \<alpha> x)"
  by (metis assms local.fFx_prop sym_type_var1)

lemma sym_face3_var1: "\<partial> (i + 1) \<alpha> (\<sigma> i (\<partial> i \<beta> x)) = \<sigma> i (\<partial> i \<alpha> (\<partial> i \<beta> x))"
proof-
  have "\<partial> (i + 1) \<alpha> (\<sigma> i (\<partial> i \<beta> x)) = \<partial> (i + 1) \<alpha> (\<sigma> i (\<partial> i \<alpha> (\<partial> i \<beta> x)))"
    by simp
  also have "\<dots> = \<sigma> i (\<partial> i \<alpha> (\<partial> i \<beta> x))"
    using local.sym_type_var1 by fastforce
  also have "\<dots> = \<sigma> i (\<partial> i \<beta> x)"
    by simp
  thus ?thesis
    using calculation by simp
qed

lemma sym_face3_simp [simp]: 
  assumes "fFx i x"
  shows "\<partial> (i + 1) \<alpha> (\<sigma> i x) = \<sigma> i x"
  by (metis assms local.fFx_prop sym_face3)

lemma sym_face3_simp_var1 [simp]: "\<partial> (i + 1) \<alpha> (\<sigma> i (\<partial> i \<beta> x)) = \<sigma> i (\<partial> i \<beta> x)"
  using sym_face3 by simp

lemma inv_sym_face3: 
  assumes "fFx (i + 1) x"
  shows "\<partial> i \<alpha> (\<theta> i x) = \<theta> i (\<partial> (i + 1) \<alpha> x)"
  by (metis assms inv_sym_type_var1 local.face_compat_var)

lemma inv_sym_face3_var1: "\<partial> i \<alpha> (\<theta> i (\<partial> (i + 1) \<beta> x)) = \<theta> i (\<partial> (i + 1) \<alpha> (\<partial> (i + 1) \<beta> x))"
  by (metis inv_sym_type_var1 local.face_compat_var)

lemma inv_sym_face3_simp: 
  assumes "fFx (i + 1) x"
  shows "\<partial> i \<alpha> (\<theta> i x) = \<theta> i x"
  using assms inv_sym_type_var local.fFx_prop by force
 
lemma inv_sym_face3_simp_var1 [simp]: "\<partial> i \<alpha> (\<theta> i (\<partial> (i + 1) \<beta> x)) = \<theta> i (\<partial> (i + 1) \<beta> x)"
  using inv_sym_face3 local.face_compat_var by simp

lemma inv_sym_face1: 
  assumes "fFx (i + 1) x"
  shows "\<partial> (i + 1) \<alpha> (\<theta> i x) = \<theta> i (\<partial> i \<alpha> x)"
  by (metis assms inv_sym_face3_simp inv_sym_sym_var1 local.face_comm_var local.sym_inv_sym sym_face1_var1)

lemma inv_sym_face1_var1: "\<partial> (i + 1) \<alpha> (\<theta> i (\<partial> (i + 1) \<beta> x)) = \<theta> i (\<partial> i \<alpha> (\<partial> (i + 1) \<beta> x))"
  using inv_sym_face1 local.face_compat_var by simp

lemma inv_sym_sym_braid: 
  assumes "diffSup i j 2"
  and "fFx j x"
  and "fFx (i + 1) x"
  shows "\<theta> i (\<sigma> j x) = \<sigma> j (\<theta> i x)"
  using assms sym_inv_sym_braid by force

lemma inv_sym_sym_braid_var1: "diffSup i j 2 \<Longrightarrow> \<theta> i (\<sigma> j (\<partial> (i + 1) \<alpha> (\<partial> j \<beta> x))) = \<sigma> j (\<theta> i (\<partial> (i + 1) \<alpha> (\<partial> j \<beta> x)))"
  using local.face_comm_var local.sym_inv_sym_braid by force

lemma inv_sym_inv_sym_braid: 
  assumes "diffSup i j 2"
  and "fFx (i + 1) x"
  and "fFx (j + 1) x"
  shows "\<theta> i (\<theta> j x) = \<theta> j (\<theta> i x)"
  by (metis Suc_eq_plus1 add_right_cancel assms inv_sym_face2 inv_sym_face3 inv_sym_sym_braid_var1 local.inv_sym_sym local.sym_inv_sym nat_le_linear not_less_eq_eq)

lemma inv_sym_inv_sym_braid_var1: "diffSup i j 2 \<Longrightarrow> \<theta> i (\<theta> j (\<partial> (i + 1) \<alpha> (\<partial> (j + 1) \<beta> x))) = \<theta> j (\<theta> i (\<partial> (i + 1) \<alpha> (\<partial> (j + 1) \<beta> x)))"
  using inv_sym_inv_sym_braid local.face_comm_var by force

text \<open>The following properties are related to symcomp and inv-symcomp.\<close>

lemma symcomp_type_var: 
  assumes "fFx i x"
  shows "fFx (i + j) (\<Sigma> i j x)" using \<open>fFx i x\<close>
  apply (induct j)
  using sym_face3 by simp_all

lemma symcomp_type: "image (\<Sigma> i j) (face_fix i) \<subseteq> face_fix (i + j)"
  using symcomp_type_var by force

lemma symcomp_type_var1 [simp]: "\<partial> (i + j) \<alpha> (\<Sigma> i j (\<partial> i \<beta> x)) = \<Sigma> i j (\<partial> i \<beta> x)"
  by (metis local.face_compat_var symcomp_type_var)

lemma inv_symcomp_type_var: 
  assumes "fFx (i + j) x"
  shows "fFx i (\<Theta> i j x)" using \<open>fFx (i + j) x\<close>
  by (induct j arbitrary: x, simp_all add: inv_sym_type_var)

lemma inv_symcomp_type: "image (\<Theta> i j) (face_fix (i + j)) \<subseteq> face_fix i"
  using inv_symcomp_type_var by force

lemma inv_symcomp_type_var1 [simp]: "\<partial> i \<alpha> (\<Theta> i j (\<partial> (i + j) \<beta> x)) = \<Theta> i j (\<partial> (i + j) \<beta> x)"
  by (meson inv_symcomp_type_var local.fFx_prop local.face_compat_var)

lemma symcomp_inv_symcomp: 
  assumes "fFx (i + j) x"
  shows "\<Sigma> i j (\<Theta> i j x) = x" using \<open>fFx (i + j) x\<close>
  by (induct j arbitrary: i x, simp_all add: inv_sym_type_var local.sym_inv_sym)

lemma inv_symcomp_symcomp: 
  assumes "fFx i x"
  shows "\<Theta> i j (\<Sigma> i j x) = x" using \<open>fFx i x\<close>
  by (induct j arbitrary: i x, simp_all add: local.inv_sym_sym symcomp_type_var)

lemma symcomp_adj: 
  assumes "fFx i x"
  and "fFx (i + j) y "
  shows "(\<Sigma> i j x = y) = (x = \<Theta> i j y)"
  using assms inv_symcomp_symcomp symcomp_inv_symcomp by force

lemma decomp_symcomp1: 
  assumes "k \<le> j" 
  and "fFx i x"
  shows " \<Sigma> i j x = \<Sigma> (i + k) (j - k) (\<Sigma> i k x)" using \<open>k \<le> j\<close>
  apply (induct j)
    using Suc_diff_le le_Suc_eq by force+

lemma decomp_symcomp2:
  assumes "k \<ge> 1"
  and "k \<le> j"
  and "fFx i x"
  shows "\<Sigma> i j x = \<Sigma> (i + k) (j - k) (\<sigma> (i + k - 1) (\<Sigma> i (k - 1) x))"
  by (metis Nat.add_diff_assoc add_diff_cancel_left' assms decomp_symcomp1 local.symcomp.simps(2) plus_1_eq_Suc)

lemma decomp_symcomp3:
  assumes "l \<ge> i"
  and "l + 1 \<le> i + j"
  and "fFx i x"
  shows "\<Sigma> i j x = \<Sigma> (l + 1) (i + j - l - 1) (\<sigma> l (\<Sigma> i (l - i) x))"
  by (smt (verit, del_insts) add.commute add_le_cancel_left assms decomp_symcomp2 diff_add_inverse2 diff_diff_left le_add1 le_add_diff_inverse)

lemma symcomp_face2: 
  assumes "l < i \<or> l > i + j"
  and  "fFx i x" 
  shows "\<partial> l \<alpha> (\<Sigma> i j x) = \<Sigma> i j (\<partial> l \<alpha> x)" using \<open>l < i \<or> l > i + j\<close>
proof (induct j)
  case 0
  show ?case 
    by simp
next
  case (Suc j)
  have "\<partial> l \<alpha> (\<Sigma> i (Suc j) x) = \<partial> l \<alpha> (\<sigma> (i + j) (\<Sigma> i j x))"
    by simp
  also have "\<dots> = \<sigma> (i + j) (\<partial> l \<alpha> (\<Sigma> i j x))"
    using Suc.prems add.commute assms(2) local.sym_face2 symcomp_type_var by auto
  also have "\<dots> = \<sigma> (i + j) (\<Sigma> i j (\<partial> l \<alpha> x))"
    using Suc.hyps Suc.prems by fastforce
  also have "\<dots> = (\<Sigma> i (Suc j) (\<partial> l \<alpha> x))"
    by simp
  finally show ?case.
qed

lemma symcomp_face3: "fFx i x \<Longrightarrow> \<partial> (i + j) \<alpha> (\<Sigma> i j x) = \<Sigma> i j (\<partial> i \<alpha> x)"
  by (metis local.face_compat_var symcomp_type_var1)

lemma symcomp_face1:
  assumes "l \<ge> i"
  and "l < i + j"
  and "fFx i x"
  shows "\<partial> l \<alpha> (\<Sigma> i j x) = \<Sigma> i j (\<partial> (l + 1) \<alpha> x)"
proof-
  have "\<partial> l \<alpha> (\<Sigma> i j x) = \<partial> l \<alpha> (\<Sigma> (l + 1) (i + j - l - 1) (\<sigma> l (\<Sigma> i (l - i) x)))"
    using Suc_eq_plus1 Suc_leI assms(1) assms(2) assms(3) decomp_symcomp3 by presburger
  also have "\<dots> = \<Sigma> (l + 1) (i + j - l - 1) (\<partial> l \<alpha> (\<sigma> l (\<Sigma> i (l - i) x)))"
    by (metis assms(1) assms(3) less_add_one ordered_cancel_comm_monoid_diff_class.add_diff_inverse sym_type_var symcomp_face2 symcomp_face3)
  also have "\<dots> = \<Sigma> (l + 1) (i + j - l - 1) (\<sigma> l (\<partial> (l + 1) \<alpha> (\<Sigma> i (l - i) x)))"
    by (metis assms(1) assms(3) local.sym_face1 ordered_cancel_comm_monoid_diff_class.add_diff_inverse symcomp_face3)
  also have "\<dots> = \<Sigma> (l + 1) (i + j - l - 1) (\<sigma> l (\<Sigma> i (l - i) (\<partial> (l + 1) \<alpha> x)))"
    by (simp add: assms(1) assms(3) symcomp_face2)
  also have "\<dots> = \<Sigma> i j (\<partial> (l + 1) \<alpha> x)"
    by (metis Suc_eq_plus1 Suc_leI assms(1) assms(2) assms(3) decomp_symcomp3 local.fFx_prop local.face_comm_var)
  finally show ?thesis.
qed

lemma inv_symcomp_face2: 
  assumes "l < i \<or> l > i + j"
  and "fFx (i + j) x"
  shows "\<partial> l \<alpha> (\<Theta> i j x) = \<Theta> i j (\<partial> l \<alpha> x)" using \<open>l < i \<or> l > i + j\<close> \<open>fFx (i + j) x\<close>
proof (induct j arbitrary: x)
  case 0
  show ?case
    using local.inv_sym_face2 by force
next
  case (Suc j)
  have h : "fFx (i + j) (\<theta> (i + j) x)"
    using Suc.prems(2) inv_sym_face3_simp by simp
  have "\<partial> l \<alpha> (\<Theta> i (Suc j) x) = \<Theta> i j (\<partial> l \<alpha> (\<theta> (i + j) x))"
    using Suc.hyps Suc.prems(1) h by force
  also have "\<dots> = \<Theta> i j (\<theta> (i + j) (\<partial> l \<alpha> x))"
    using Suc.prems inv_sym_face2 by force
  also have "\<dots> = (\<Theta> i (Suc j) (\<partial> l \<alpha> x))"
    by simp
  finally show ?case.
qed

lemma inv_symcomp_face3: "fFx (i + j) x \<Longrightarrow> \<partial> i \<alpha> (\<Theta> i j x) = \<Theta> i j (\<partial> (i + j) \<alpha> x)"
  by (metis inv_symcomp_type_var1 local.face_compat_var)

lemma inv_symcomp_face1:
  assumes "l > i"
  and "l \<le> i + j"
  and "fFx (i + j) x"
  shows "\<partial> l \<alpha> (\<Theta> i j x) = \<Theta> i j (\<partial> (l - 1) \<alpha> x)"
proof-
  have "(\<partial> l \<alpha> (\<Theta> i j x) = \<Theta> i j (\<partial> (l - 1) \<alpha> x)) = (\<Sigma> i j (\<partial> l \<alpha> (\<Theta> i j x)) = \<partial> (l - 1) \<alpha> x)"
    by (smt (z3) assms(3) inv_symcomp_face3 local.fFx_prop local.face_comm_var symcomp_adj)
  also have "\<dots> = (\<partial> (l - 1) \<alpha> (\<Sigma> i j (\<Theta> i j x)) = \<partial> (l - 1) \<alpha> x)"
    using assms(1) assms(2) assms(3) inv_symcomp_type_var symcomp_face1 by force
  also have "\<dots> = True"
    using assms(3) symcomp_inv_symcomp by auto
  finally show ?thesis
    by simp
qed

lemma symcomp_comp1: 
  assumes "fFx i x"
  and "fFx i y"
  and "DD i x y"
  shows "\<Sigma> i j (x \<otimes>\<^bsub>i\<^esub> y) = \<Sigma> i j x \<otimes>\<^bsub>(i + j)\<^esub> \<Sigma> i j y"
  by (induct j, simp, metis assms local.face_compat_var local.iDst local.icat.sscatml.r0_absorb symcomp_type_var1)

lemma symcomp_comp2: 
  assumes "k < i"
  and "fFx i x"
  and "fFx i y"
  and "DD k x y"
  shows "\<Sigma> i j (x \<otimes>\<^bsub>k\<^esub> y) = \<Sigma> i j x \<otimes>\<^bsub>k\<^esub> \<Sigma> i j y"
proof (induct j)
  case 0
  show ?case
    by simp
next
  case (Suc j)
  have "\<Sigma> i (Suc j) (x\<otimes>\<^bsub>k\<^esub>y) = \<sigma> (i + j) (\<Sigma> i j (x\<otimes>\<^bsub>k\<^esub>y))"
    by simp
  also have "\<dots> = \<sigma> (i + j) ((\<Sigma> i j x) \<otimes>\<^bsub>k\<^esub> (\<Sigma> i j y))"
    by (simp add: Suc)
  also have "\<dots> = \<sigma> (i + j) (\<Sigma> i j x) \<otimes>\<^bsub>k\<^esub> \<sigma> (i + j) (\<Sigma> i j y)"
    apply (rule sym_func3)
    using assms(1) assms(2) assms(3) symcomp_type_var apply presburger+
    using assms(1) assms(2) assms(3) assms(4) local.iDst local.locality symcomp_face2 by presburger
  also have "\<dots> = \<Sigma> i (Suc j) x \<otimes>\<^bsub>k\<^esub> \<Sigma> i (Suc j) y"
    by simp
  finally show ?case.
qed

lemma symcomp_comp3: 
  assumes "k > i + j"
  and "fFx i x"
  and "fFx i y"
  and "DD k x y"
  shows "\<Sigma> i j (x \<otimes>\<^bsub>k\<^esub> y) = \<Sigma> i j x \<otimes>\<^bsub>k\<^esub> \<Sigma> i j y" using \<open>k > i + j\<close>
proof (induct j)
  case 0
  show ?case
    by simp
next
  case (Suc j)
  have "\<Sigma> i (Suc j) (x\<otimes>\<^bsub>k\<^esub>y) = \<sigma> (i + j) ((\<Sigma> i j x) \<otimes>\<^bsub>k\<^esub> (\<Sigma> i j y))"
    using Suc.hyps Suc.prems by force
  also have "\<dots> = \<sigma> (i + j) (\<Sigma> i j x) \<otimes>\<^bsub>k\<^esub> \<sigma> (i + j) (\<Sigma> i j y)"
    apply (rule sym_func3)
    using Suc.prems apply linarith+
    using assms(2) assms(3) symcomp_type_var apply presburger+
    using Suc.prems assms(2) assms(3) assms(4) local.icid.ts_msg.st_locality_locality symcomp_face2 by simp
  also have "\<dots> = \<Sigma> i (Suc j) x \<otimes>\<^bsub>k\<^esub> \<Sigma> i (Suc j) y"
    by simp
  finally show ?case.
qed

lemma fix_comp:
  assumes "i \<noteq> j"
  and "fFx i x"
  and "fFx i y"
  and "DD j x y"
  shows "fFx i (x \<otimes>\<^bsub>j\<^esub> y)"
  using face_func assms by simp

lemma symcomp_comp4: 
  assumes "i < k"
  and "k \<le> i + j"
  and "fFx i x"
  and "fFx i y"
  and "DD k x y"
  shows "\<Sigma> i j (x \<otimes>\<^bsub>k\<^esub> y) = \<Sigma> i j x \<otimes>\<^bsub>(k - 1)\<^esub> \<Sigma> i j y" 
  using \<open>k \<le> i + j\<close> \<open>fFx i x\<close> \<open>fFx i y\<close> \<open>DD k x y\<close>
proof (induct j arbitrary: x y)
  case 0
  thus ?case
    using assms(1) by linarith
next
  case (Suc j)
  have a: "fFx i (x \<otimes>\<^bsub>k\<^esub> y)"
    using Suc.prems(2) Suc.prems(3) Suc.prems(4) assms(1) fix_comp by force
  have b: "fFx (k - 1) (\<Sigma> i (k - 1 - i) x)"
    using Suc.prems(2) assms(1) less_imp_Suc_add symcomp_type_var by fastforce
  have c: "fFx (k - 1) (\<Sigma> i (k - 1 - i) y)"
    using Suc.prems(3) assms(1) less_imp_Suc_add symcomp_type_var by fastforce
  have d: "DD k (\<Sigma> i (k - 1 - i) x) (\<Sigma> i (k - 1 - i) y)"
    by (metis Suc.prems(2) Suc.prems(3) Suc.prems(4) add_diff_cancel_left' assms(1) lessI less_imp_Suc_add local.iDst local.locality plus_1_eq_Suc symcomp_face2)
  have "\<Sigma> i (Suc j) (x \<otimes>\<^bsub>k\<^esub> y) = \<Sigma> k (i + j + 1 - k) (\<sigma> (k - 1) (\<Sigma> i (k - 1 - i) (x \<otimes>\<^bsub>k\<^esub> y)))"
    by (smt (verit) Suc.prems(1) Suc_eq_plus1 a add_Suc_right add_le_imp_le_diff assms(1) decomp_symcomp3 diff_diff_left le_add_diff_inverse2 less_eq_Suc_le plus_1_eq_Suc)
  also have "\<dots> = \<Sigma> k (i + j + 1 - k) (\<sigma> (k - 1) (\<Sigma> i (k - 1 - i) x \<otimes>\<^bsub>k\<^esub> \<Sigma> i (k - 1 - i) y))"
    using Suc.prems(2) Suc.prems(3) Suc.prems(4) assms(1) symcomp_comp3 by force
  also have "\<dots> = \<Sigma> k (i + j + 1 - k) (\<sigma> (k - 1) (\<Sigma> i (k - 1 - i) x \<otimes>\<^bsub>((k - 1) + 1)\<^esub> \<Sigma> i (k - 1 - i) y))"
    using assms(1) by auto
  also have "\<dots> = \<Sigma> k (i + j + 1 - k) (\<sigma> (k - 1) (\<Sigma> i (k - 1 - i) x) \<otimes>\<^bsub>(k - 1)\<^esub> \<sigma> (k - 1) (\<Sigma> i (k - 1 - i) y))"
    using assms(1) b c d less_iff_Suc_add sym_func2 by fastforce
  also have "\<dots> = \<Sigma> k (i + j + 1 - k) (\<sigma> (k - 1) (\<Sigma> i (k - 1 - i) x)) \<otimes>\<^bsub>(k - 1)\<^esub> \<Sigma> k (i + j + 1 - k) (\<sigma> (k - 1) (\<Sigma> i (k - 1 - i) y))"
    apply (rule symcomp_comp2)
    using assms(1) b sym_face3 apply fastforce+
    apply (metis assms(1) c le_add1 le_add_diff_inverse2 less_imp_Suc_add plus_1_eq_Suc sym_face3)
    by (metis assms(1) b c d le_add1 le_add_diff_inverse2 less_imp_Suc_add plus_1_eq_Suc sym_func2_DD)
  also have "\<dots> = \<Sigma> k (i + j + 1 - k) (\<Sigma> i (k - i) x) \<otimes>\<^bsub>(k - 1)\<^esub> \<Sigma> k (i + j + 1 - k) (\<Sigma> i (k - i) y)"
    using assms(1) less_imp_Suc_add by fastforce
  also have "\<dots> = (\<Sigma> i (j+1) x) \<otimes>\<^bsub>(k - 1)\<^esub> \<Sigma> k (i + j + 1 - k) (\<Sigma> i (k - i) y)"
    by (smt (verit, ccfv_SIG) Nat.diff_diff_eq Suc.prems(1) Suc.prems(2) add.comm_neutral add_left_mono assms(1) decomp_symcomp1 diff_add_inverse diff_le_mono group_cancel.add2 linordered_semidom_class.add_diff_inverse order_less_imp_le order_less_imp_not_less plus_1_eq_Suc zero_less_Suc)
  also have "\<dots> = (\<Sigma> i (j + 1) x) \<otimes>\<^bsub>(k - 1)\<^esub> (\<Sigma> i (j + 1) y)"
    by (smt (verit, ccfv_SIG) Nat.add_0_right Nat.diff_diff_eq Suc.prems(1) Suc.prems(3) add_Suc add_Suc_shift add_diff_inverse_nat add_mono_thms_linordered_semiring(2) assms(1) decomp_symcomp1 diff_add_inverse diff_le_mono nless_le order.asym plus_1_eq_Suc trans_less_add2 zero_less_one)
  finally show ?case
    by simp
qed

lemma symcomp_comp: 
  assumes "fFx i x"
  and "fFx i y"
  and "DD k x y"
  shows "\<Sigma> i j (x \<otimes>\<^bsub>k\<^esub> y) = (if k = i then \<Sigma> i j x \<otimes>\<^bsub>(i + j)\<^esub> \<Sigma> i j y
                                else (if (i < k \<and> k \<le> i + j) then \<Sigma> i j x \<otimes>\<^bsub>(k - 1)\<^esub> \<Sigma> i j y
                                  else \<Sigma> i j x \<otimes>\<^bsub>k\<^esub> \<Sigma> i j y))"
  by (metis assms linorder_not_le not_less_iff_gr_or_eq symcomp_comp1 symcomp_comp2 symcomp_comp3 symcomp_comp4)

lemma inv_symcomp_comp1: 
  assumes "fFx (i + j) x"
  and "fFx (i + j) y"
  and "DD (i + j) x y"
  shows "\<Theta> i j (x \<otimes>\<^bsub>(i + j)\<^esub> y) = \<Theta> i j x \<otimes>\<^bsub>i\<^esub> \<Theta> i j y"
  by (metis assms inv_symcomp_type_var local.fFx_prop local.iDst local.icat.sscatml.l0_absorb)

lemma inv_symcomp_comp2:
  assumes "k < i"
  and "fFx (i + j) x"
  and "fFx (i + j) y"
  and "DD k x y"
  shows "\<Theta> i j (x \<otimes>\<^bsub>k\<^esub> y) = \<Theta> i j x \<otimes>\<^bsub>k\<^esub> \<Theta> i j y"
proof-
  have h1: "fFx (i + j) (x \<otimes>\<^bsub>k\<^esub> y)"
    using assms(1) assms(2) assms(3) assms(4) fix_comp by force
  have h2: "fFx i (\<Theta> i j x)"
    using assms(2) inv_symcomp_type_var by auto
  have h3: "fFx i (\<Theta> i j y)"
    using assms(3) inv_symcomp_type_var by auto
  have h4: "DD k (\<Theta> i j x) (\<Theta> i j y)"
    using assms(1) assms(2) assms(3) assms(4) inv_symcomp_face2 local.iDst local.locality by presburger
  hence h5: "fFx i ((\<Theta> i j x) \<otimes>\<^bsub>k\<^esub> (\<Theta> i j y))"
    using h2 h3 fix_comp assms(1) by force
  have "(\<Theta> i j (x \<otimes>\<^bsub>k\<^esub> y) = (\<Theta> i j x) \<otimes>\<^bsub>k\<^esub> (\<Theta> i j y)) = (x \<otimes>\<^bsub>k\<^esub> y = \<Sigma> i j ((\<Theta> i j x) \<otimes>\<^bsub>k\<^esub> (\<Theta> i j y)))"
    by (metis symcomp_adj h1 h5)
  also have "\<dots> = (x \<otimes>\<^bsub>k\<^esub> y = \<Sigma> i j (\<Theta> i j x) \<otimes>\<^bsub>k\<^esub> \<Sigma> i j (\<Theta> i j y))"
    by (simp add: assms(1) h2 h3 h4 symcomp_comp2)
  also have "\<dots> = True"
    using assms(2) assms(3) symcomp_inv_symcomp by force
  finally show ?thesis
    by simp
qed

lemma inv_symcomp_comp3:
  assumes "k > i + j"
  and "fFx (i + j) x"
  and "fFx (i + j) y"
  and "DD k x y"
  shows "\<Theta> i j (x \<otimes>\<^bsub>k\<^esub> y) = \<Theta> i j x \<otimes>\<^bsub>k\<^esub> \<Theta> i j y"
proof-
  have h1: "fFx (i + j) (x \<otimes>\<^bsub>k\<^esub> y)"
    using assms(1) assms(2) assms(3) assms(4) fix_comp by force
  have h2: "fFx i (\<Theta> i j x)"
    using assms(2) inv_symcomp_type_var by auto
  have h3: "fFx i (\<Theta> i j y)"
    using assms(3) inv_symcomp_type_var by auto
  have h4: "DD k (\<Theta> i j x) (\<Theta> i j y)"
    using assms(1) assms(2) assms(3) assms(4) inv_symcomp_face2 local.iDst local.locality by presburger
  hence h5: "fFx i ((\<Theta> i j x) \<otimes>\<^bsub>k\<^esub> (\<Theta> i j y))"
    using h2 h3 fix_comp assms(1) by force
  have "(\<Theta> i j (x \<otimes>\<^bsub>k\<^esub> y) = (\<Theta> i j x) \<otimes>\<^bsub>k\<^esub> (\<Theta> i j y)) = (x \<otimes>\<^bsub>k\<^esub> y = \<Sigma> i j ((\<Theta> i j x) \<otimes>\<^bsub>k\<^esub> (\<Theta> i j y)))"
    by (metis symcomp_adj h1 h5)
  also have "\<dots> = (x \<otimes>\<^bsub>k\<^esub> y = \<Sigma> i j (\<Theta> i j x) \<otimes>\<^bsub>k\<^esub> \<Sigma> i j (\<Theta> i j y))"
    by (simp add: assms(1) h2 h3 h4 symcomp_comp3)
  also have "\<dots> = True"
    using assms(2) assms(3) symcomp_inv_symcomp by force
  finally show ?thesis
    by simp
qed

lemma inv_symcomp_comp4:
  assumes "i \<le> k"
  and "k < i + j"
  and "fFx (i + j) x"
  and "fFx (i + j) y"
  and "DD k x y"
  shows "\<Theta> i j (x \<otimes>\<^bsub>k\<^esub> y) = \<Theta> i j x \<otimes>\<^bsub>(k + 1)\<^esub> \<Theta> i j y"
proof-
  have h1: "fFx (i + j) (x \<otimes>\<^bsub>k\<^esub> y)"
    using assms(2) assms(3) assms(4) assms(5) fix_comp by force
  have h2: "fFx i (\<Theta> i j x)"
    using assms(3) inv_symcomp_type_var by auto
  have h3: "fFx i (\<Theta> i j y)"
    using assms(4) inv_symcomp_type_var by auto
  have h4: "DD (k + 1) (\<Theta> i j x) (\<Theta> i j y)"
    using assms(1) assms(2) assms(3) assms(4) assms(5) inv_symcomp_face1 local.icat.sts_msg.st_local by auto
  hence h5: "fFx i ((\<Theta> i j x) \<otimes>\<^bsub>(k + 1)\<^esub> (\<Theta> i j y))"
    using h2 h3 fix_comp assms(1) assms(2) by force
  have "(\<Theta> i j (x \<otimes>\<^bsub>k\<^esub> y) = (\<Theta> i j x) \<otimes>\<^bsub>(k + 1)\<^esub> (\<Theta> i j y)) = (x \<otimes>\<^bsub>k\<^esub> y = \<Sigma> i j ((\<Theta> i j x) \<otimes>\<^bsub>(k + 1)\<^esub> (\<Theta> i j y)))"
    by (metis symcomp_adj h1 h5)
  also have "\<dots> = (x \<otimes>\<^bsub>k\<^esub> y = \<Sigma> i j (\<Theta> i j x) \<otimes>\<^bsub>k\<^esub> \<Sigma> i j (\<Theta> i j y))"
    apply (subst symcomp_comp4)
    using assms(1) assms(2) h2 h3 h4 by auto[6]
  also have "\<dots> = True"
    using assms(3) assms(4) symcomp_inv_symcomp by force
  finally show ?thesis
    by simp
qed

end


subsection \<open>Cubical $\omega$-categories with connections\<close>

class connection_ops = 
  fixes connection :: "nat \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("\<Gamma>")

abbreviation (in connection_ops) "\<Gamma>\<Gamma> i \<alpha> \<equiv> image (\<Gamma> i \<alpha>)"

text \<open>We define a class for cubical $\omega$-categories with connections.\<close>

class cubical_omega_category_connections = cubical_omega_category + connection_ops +
  assumes conn_face1: "fFx j x \<Longrightarrow> \<partial> j \<alpha> (\<Gamma> j \<alpha> x) = x"
  and conn_face2: "fFx j x \<Longrightarrow> \<partial> (j + 1) \<alpha> (\<Gamma> j \<alpha> x) = \<sigma> j x"
  and conn_face3: "i \<noteq> j \<Longrightarrow> i \<noteq> j + 1 \<Longrightarrow> fFx j x \<Longrightarrow> \<partial> i \<alpha> (\<Gamma> j \<beta> x) = \<Gamma> j \<beta> (\<partial> i \<alpha> x)"
  and conn_corner1: "fFx i x \<Longrightarrow> fFx i y \<Longrightarrow> DD (i + 1) x y \<Longrightarrow> \<Gamma> i tt (x \<otimes>\<^bsub>(i + 1)\<^esub> y) = (\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i x) \<otimes>\<^bsub>i\<^esub> (x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)" 
  and conn_corner2: "fFx i x \<Longrightarrow> fFx i y \<Longrightarrow> DD (i + 1) x y \<Longrightarrow> \<Gamma> i ff (x \<otimes>\<^bsub>(i + 1)\<^esub> y) = (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> y) \<otimes>\<^bsub>i\<^esub> (\<sigma> i y \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y)"
  and conn_corner3: "j \<noteq> i \<and> j \<noteq> i + 1 \<Longrightarrow> fFx i x \<Longrightarrow> fFx i y \<Longrightarrow> DD j x y \<Longrightarrow> \<Gamma> i \<alpha> (x \<otimes>\<^bsub>j\<^esub> y) = \<Gamma> i \<alpha> x \<otimes>\<^bsub>j\<^esub> \<Gamma> i \<alpha> y"
  and conn_fix: "fFx i x \<Longrightarrow> fFx (i + 1) x \<Longrightarrow> \<Gamma> i \<alpha> x = x"
  and conn_zigzag1: "fFx i x \<Longrightarrow> \<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff x = x"
  and conn_zigzag2: "fFx i x \<Longrightarrow> \<Gamma> i tt x \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff x = \<sigma> i x"
  and conn_conn_braid: "diffSup i j 2 \<Longrightarrow> fFx j x \<Longrightarrow> fFx i x \<Longrightarrow> \<Gamma> i \<alpha> (\<Gamma> j \<beta> x) = \<Gamma> j \<beta> (\<Gamma> i \<alpha> x)"
  and conn_shift: "fFx i x \<Longrightarrow> fFx (i + 1) x \<Longrightarrow> \<sigma> (i + 1) (\<sigma> i (\<Gamma> (i + 1) \<alpha> x)) = \<Gamma> i \<alpha> (\<sigma> (i + 1) x)"

begin 

lemma conn_face4: "fFx j x \<Longrightarrow> \<partial> j \<alpha> (\<Gamma> j (\<not>\<alpha>) x) = \<partial> (j + 1) \<alpha> x"
  by (smt (z3) local.conn_face1 local.conn_zigzag2 local.face_comm_var local.locality local.pcomp_lface local.pcomp_uface local.sym_face1 local.sym_fix_var1)

lemma conn_face1_lift: "FFx j X \<Longrightarrow> \<partial>\<partial> j \<alpha> (\<Gamma>\<Gamma> j \<alpha> X) = X"
  by (auto simp add: image_iff local.conn_face1)

lemma conn_face4_lift: "FFx j X \<Longrightarrow> \<partial>\<partial> j \<alpha> (\<Gamma>\<Gamma> j (\<not>\<alpha>) X) = \<partial>\<partial> (j + 1) \<alpha> X"
  apply safe
  apply (simp add: local.conn_face4)
  by (metis image_eqI local.conn_face4)

lemma conn_face2_lift: "FFx j X \<Longrightarrow> \<partial>\<partial> (j + 1) \<alpha> (\<Gamma>\<Gamma> j \<alpha> X) = \<sigma>\<sigma> j X"
  by (smt (z3) comp_apply image_comp image_cong local.conn_face2)

lemma conn_face3_lift: "i \<noteq> j \<Longrightarrow> i \<noteq> j + 1 \<Longrightarrow> FFx j X \<Longrightarrow> \<partial>\<partial> i \<alpha> (\<Gamma>\<Gamma> j \<beta> X) = \<Gamma>\<Gamma> j \<beta> (\<partial>\<partial> i \<alpha> X)"
  by (smt (z3) image_cong image_image local.conn_face3)

lemma conn_fix_lift: "FFx i X \<Longrightarrow> FFx (i + 1) X \<Longrightarrow> \<Gamma>\<Gamma> i \<alpha> X = X"
  by (simp add: local.conn_fix)

lemma conn_conn_braid_lift: "diffSup i j 2 \<Longrightarrow> FFx j X \<Longrightarrow> FFx i X \<Longrightarrow> \<Gamma>\<Gamma> i \<alpha> (\<Gamma>\<Gamma> j \<beta> X) = \<Gamma>\<Gamma> j \<beta> (\<Gamma>\<Gamma> i \<alpha> X)"
  by (smt (z3) image_cong image_image local.conn_conn_braid)

lemma conn_sym_braid: "diffSup i j 2 \<Longrightarrow> fFx i x \<Longrightarrow> fFx j x \<Longrightarrow> \<Gamma> i \<alpha> (\<sigma> j x) = \<sigma> j (\<Gamma> i \<alpha> x)"
  by (smt (z3) add_diff_cancel_left' cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' icat.st_local le_add1 local.conn_conn_braid local.conn_corner3 local.conn_face1 local.conn_face3 local.conn_zigzag2 numeral_le_one_iff rel_simps(28) semiring_norm(69))

lemma conn_zigzag1_var [simp]: "\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x) = {\<partial> i \<alpha> x}"
proof (cases "DD (i + 1) (\<Gamma> i tt (\<partial> i \<alpha> x)) (\<Gamma> i ff (\<partial> i \<alpha> x))")
  case True
  hence "\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x) = {\<Gamma> i tt (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x)}"
    by (metis True local.icat.pcomp_def_var4)
  also have "\<dots> = {\<partial> i \<alpha> x}"
    using local.conn_zigzag1 by simp
  finally show ?thesis.
next
  case False
  thus ?thesis
    using local.conn_face2 local.locality by simp 
qed

lemma conn_zigzag1_lift:
  assumes "FFx i X"
  shows "\<Gamma>\<Gamma> i tt X \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i ff X = X"
proof-
  have "\<Gamma>\<Gamma> i tt X \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i ff X = {\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> DD (i + 1) (\<Gamma> i tt x) (\<Gamma> i ff y)}"
    unfolding local.iconv_prop by force
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> \<partial> (i + 1) tt (\<Gamma> i tt x) = \<partial> (i + 1) ff (\<Gamma> i ff y)}"
    using icat.st_local by presburger
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> \<sigma> i x = \<sigma> i y}"
    by (metis (no_types, lifting) assms local.conn_face2)
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> x = y}"
    by (metis assms local.inv_sym_sym_var1)
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff x | x. x \<in> X}"
    by simp
  also have "\<dots> = {\<Gamma> i tt (\<partial> i tt x) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i tt x) | x. x \<in> X}"
    by (metis (full_types) assms icid.ts_compat)
  also have "\<dots> = {\<partial> i tt x | x. x \<in> X}"
    using local.conn_zigzag1 local.face_compat_var by presburger
  also have "\<dots> = X"
    by (smt (verit, del_insts) Collect_cong Collect_mem_eq assms local.icid.stopp.st_fix)
  finally show ?thesis.
qed

lemma conn_zigzag2_var: "\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x) = {\<sigma> i (\<partial> i \<alpha> x)}"
proof (cases "DD i (\<Gamma> i tt (\<partial> i \<alpha> x)) (\<Gamma> i ff (\<partial> i \<alpha> x))")
  case True
  hence "\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x) = {\<Gamma> i tt (\<partial> i \<alpha> x) \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<alpha> x)}"
    by (metis True local.icat.pcomp_def_var4)
  also have "\<dots> = {\<sigma> i (\<partial> i \<alpha> x)}"
    using local.conn_zigzag2 by simp
  finally show ?thesis.
next
  case False
  thus ?thesis
    by (simp add: local.conn_face1 local.locality)
qed

lemma conn_zigzag2_lift:
  assumes "FFx i X"
  shows "\<Gamma>\<Gamma> i tt X \<star>\<^bsub>i\<^esub> \<Gamma>\<Gamma> i ff X = \<sigma>\<sigma> i X"
proof-
  have "\<Gamma>\<Gamma> i tt X \<star>\<^bsub>i\<^esub> \<Gamma>\<Gamma> i ff X = {\<Gamma> i tt x \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> DD i (\<Gamma> i tt x) (\<Gamma> i ff y)}"
    unfolding local.iconv_prop by force
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> \<partial> i tt (\<Gamma> i tt x) = \<partial> i ff (\<Gamma> i ff y)}"
    using icat.st_local by presburger
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff y | x y. x \<in> X \<and> y \<in> X \<and> x = y}"
    using assms local.conn_face1 by force
  also have "\<dots> = {\<Gamma> i tt x \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff x | x. x \<in> X}"
    by simp
  also have "\<dots> = {\<Gamma> i tt (\<partial> i tt x) \<otimes>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i tt x) | x. x \<in> X}"
    by (metis (full_types) assms icid.ts_compat)
  also have "\<dots> = {\<sigma> i x | x. x \<in> X}"
    by (metis assms icid.ts_compat local.conn_zigzag2)
  also have "\<dots> = \<sigma>\<sigma> i X"
    by force
  finally show ?thesis.
qed

lemma conn_sym_braid_lift: "diffSup i j 2 \<Longrightarrow> FFx i X \<Longrightarrow> FFx j X \<Longrightarrow> \<Gamma>\<Gamma> i \<alpha> (\<sigma>\<sigma> j X) = \<sigma>\<sigma> j (\<Gamma>\<Gamma> i \<alpha> X)"
  by (smt (z3) image_cong image_image local.conn_sym_braid)

lemma conn_corner1_DD:
  assumes "fFx i x"
  and "fFx i y"
  and "DD (i + 1) x y"
  shows "DD i (\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i x) (x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)"
proof-
  have h1: "DD (i + 1) (\<Gamma> i tt x) (\<sigma> i x)"
    using assms(1) local.conn_face2 local.locality local.sym_type_var by simp
  have h2: "DD (i + 1) x (\<Gamma> i tt y)"
    by (metis assms(2) assms(3) conn_zigzag1_var icat.st_local icid.src_comp_aux singleton_iff)
  have h3: "\<partial> i tt (\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i x) = x"
    by (metis assms(1) local.conn_face1 local.conn_face2 local.icat.sscatml.r0_absorb)
  have "\<partial> i ff (x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) = \<partial> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i tt y)"
    using h2 local.face_func by simp
  hence h4: "\<partial> i ff (x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) = x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> (i + 1) ff y"
    by (metis (full_types) assms(1) assms(2) local.conn_face4)
  have "\<partial> i tt (\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i x) = \<partial> i tt (\<Gamma> i tt x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<sigma> i x)"
    using h1 local.face_func by simp
  also have "\<dots> = x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> (i + 1) tt x"
    using calculation h3 by simp
  thus ?thesis
    using assms(3) h3 h4 local.icat.sts_msg.st_local by simp
qed

lemma conn_corner1_var: "\<Gamma>\<Gamma> i tt (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = (\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<sigma> i (\<partial> i \<alpha> x)) \<star>\<^bsub>i\<^esub> (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt (\<partial> i \<beta> y))"
proof (cases "DD (i + 1) (\<partial> i \<alpha> x) (\<partial> i \<beta> y)")
  case True
  have h1: "DD (i + 1) (\<Gamma> i tt (\<partial> i \<alpha> x)) (\<sigma> i (\<partial> i \<alpha> x))"
    by (metis local.conn_face2 local.face_compat_var local.locality)
  have h2: "DD (i + 1) (\<partial> i \<alpha> x) (\<Gamma> i tt (\<partial> i \<beta> y))"
    by (metis True icid.src_comp_aux insertCI local.conn_zigzag1_var local.iDst local.locality)
  have h3: "DD i (\<Gamma> i tt (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i (\<partial> i \<alpha> x)) (\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt (\<partial> i \<beta> y))"
    using True local.conn_corner1_DD local.face_compat_var by simp
  have "\<Gamma>\<Gamma> i tt (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = \<Gamma>\<Gamma> i tt {\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y}"
    using True local.icat.pcomp_def_var4 by simp
  also have "\<dots> = {(\<Gamma> i tt (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i (\<partial> i \<alpha> x)) \<otimes>\<^bsub>i\<^esub> (\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt (\<partial> i \<beta> y))}"
    using True local.conn_corner1 local.face_compat_var by simp
  also have "\<dots> = {\<Gamma> i tt (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i (\<partial> i \<alpha> x)} \<star>\<^bsub>i\<^esub> {\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt (\<partial> i \<beta> y)}"
    using h3 local.icat.pcomp_def_var4 local.icid.stopp.conv_atom by simp
  also have "\<dots> = (\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<sigma> i (\<partial> i \<alpha> x)) \<star>\<^bsub>i\<^esub> (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt (\<partial> i \<beta> y))"
    using h1 h2 local.icat.pcomp_def_var4 by simp
  finally show ?thesis.
next
  case False
  thus ?thesis
    by (smt (z3) Union_empty empty_is_image icat.st_local icid.ts_compat local.conn_face4 local.face_comm_var local.icid.stopp.ts_compat multimagma.conv_distl)
qed

lemma conn_corner1_lift_aux: "fFx i x \<Longrightarrow> \<partial> (i + 1) ff (\<Gamma> i tt x) = \<partial> (i + 1) ff x"
  by (metis conn_zigzag1_var empty_not_insert equals0I icid.src_comp_aux singletonD)

lemma conn_corner1_lift:
  assumes "FFx i X"
  and "FFx i Y"
  shows "\<Gamma>\<Gamma> i tt (X \<star>\<^bsub>(i + 1)\<^esub> Y) = (\<Gamma>\<Gamma> i tt X \<star>\<^bsub>(i + 1)\<^esub> \<sigma>\<sigma> i X) \<star>\<^bsub>i\<^esub> (X \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i tt Y)"
proof-
  have h1: "\<forall>y \<in> Y. \<partial> (i + 1) ff (\<Gamma> i tt y) = \<partial> (i + 1) ff y"
    by (metis assms(2) conn_zigzag1_var local.icid.ts_msg.tgt_comp_aux singletonI)
  have h2 :"\<forall>xa \<in> X. DD (i + 1) (\<Gamma> i tt xa) (\<sigma> i xa) \<longrightarrow> \<partial> i tt (\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) = \<partial> i tt (\<Gamma> i tt xa) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<sigma> i xa)"
    by (simp add: local.face_func)
  have h3 :"\<forall>xc \<in> X. \<forall>y \<in> Y. DD (i + 1) xc (\<Gamma> i tt y) \<longrightarrow> \<partial> i ff (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) = \<partial> i ff xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i tt y)"
    by (simp add: local.face_func)
  have h4: "\<forall>xa \<in> X. \<partial> i tt (\<Gamma> i tt xa) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<sigma> i xa) = xa \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<partial> (i + 1) tt xa)"
    by (smt (z3) assms(1) local.conn_face1 local.fFx_prop local.face_comm_var local.sym_face1_var1 local.sym_fix_var1)
  have h5: "\<forall>xc \<in> X. \<forall>y \<in> Y. \<partial> i ff xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i tt y) = xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> (i + 1) ff y"
    by (metis (full_types) assms(1) assms(2) local.conn_face4)
  have h6: "\<forall>xc \<in> X. \<forall>y \<in> Y. DD (i + 1) xc (\<partial> (i + 1) ff y) \<longrightarrow> xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> (i + 1) ff y = xc"
    by (metis local.face_compat_var local.icat.sscatml.r0_absorb local.icid.stopp.Dst)
  have h7: "\<forall>xa \<in> X. xa \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<partial> (i + 1) tt xa) = xa"
    by (metis assms(1) local.face_comm_var local.face_compat_var local.icat.sscatml.r0_absorb)
  have h8: "\<forall>x \<in> X. \<forall>y \<in> Y. DD (i + 1) x y \<longrightarrow> (\<Gamma> i tt x \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i x) \<otimes>\<^bsub>i\<^esub> (x \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) = \<Gamma> i tt (x \<otimes>\<^bsub>(i + 1)\<^esub> y)"
    using assms(1) assms(2) local.conn_corner1 by auto
  have "(\<Gamma>\<Gamma> i tt X \<star>\<^bsub>(i + 1)\<^esub> \<sigma>\<sigma> i X) \<star>\<^bsub>i\<^esub> (X \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i tt Y) = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xb xc y. xa \<in> X \<and> xb \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> DD (i + 1) (\<Gamma> i tt xa) (\<sigma> i xb) \<and> DD (i + 1) xc (\<Gamma> i tt y) \<and> DD i (\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)}"
    unfolding local.iconv_prop by blast
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xb xc y. xa \<in> X \<and> xb \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> \<partial> (i + 1) tt (\<Gamma> i tt xa) = \<partial> (i + 1) ff (\<sigma> i xb) \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff (\<Gamma> i tt y) \<and> \<partial> i tt (\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) = \<partial> i ff (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)}"
    using icat.st_local by presburger
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xb xc y. xa \<in> X \<and> xb \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> xa = xb \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff (\<Gamma> i tt y) \<and> \<partial> i tt (\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xb) = \<partial> i ff (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)}"
    by (smt (verit) Collect_cong assms(1) local.conn_face2 local.sym_type_var)
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xc y. xa \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff y \<and> \<partial> i tt (\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) = \<partial> i ff (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y)}"
    by (smt (verit, best) Collect_cong assms(1) h1 local.conn_face3 local.locality local.sym_type_var)
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xc y. xa \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff y \<and> \<partial> i tt (\<Gamma> i tt xa) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<sigma> i xa) = \<partial> i ff xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i tt y)}"
    by (smt (verit, del_insts) h2 h3 Collect_cong assms(1) h1 icat.st_local local.conn_face2 local.sym_type_var)
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xc y. xa \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff y \<and> xa \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt (\<partial> (i + 1) tt xa) = xc \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> (i + 1) ff y}"
    by (smt (verit, del_insts) h4 h5 Collect_cong)
  also have "\<dots> = {(\<Gamma> i tt xa \<otimes>\<^bsub>(i + 1)\<^esub> \<sigma> i xa) \<otimes>\<^bsub>i\<^esub> (xc \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i tt y) | xa xc y. xa \<in> X \<and> xc \<in> X \<and> y \<in> Y \<and> \<partial> (i + 1) tt xc = \<partial> (i + 1) ff y \<and> xa = xc}"
    by (smt (z3) h6 h7 Collect_cong assms(2) icid.st_eq1 local.face_comm_var)
  also have "\<dots> = {\<Gamma> i tt (x \<otimes>\<^bsub>(i + 1)\<^esub> y) | x y. x \<in> X \<and> y \<in> Y \<and> DD (i + 1) x y}"
    by (smt (verit, ccfv_threshold) h8 Collect_cong icat.st_local)
  also have "\<dots> = \<Gamma>\<Gamma> i tt (X \<star>\<^bsub>(i + 1)\<^esub> Y)"
    unfolding local.iconv_prop by force
  finally show ?thesis
    by simp
qed

lemma conn_corner2_DD:
  assumes "fFx i x"
  and "fFx i y"
  and "DD (i + 1) x y"
  shows "DD i (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> y) (\<sigma> i y \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y)"
proof-
  have h1: "DD (i + 1) (\<Gamma> i ff x) y"
    by (metis assms(1) assms(3) conn_zigzag1_var insertCI local.iDst local.icid.ts_msg.src_comp_aux local.locality)
  have h2: "DD (i + 1) (\<sigma> i y) (\<Gamma> i ff y)"
    by (metis assms(2) local.conn_face2 local.face_compat_var local.locality)
  have h3: "\<partial> i ff (\<sigma> i y \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y) = \<partial> i ff (\<sigma> i y) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i ff y)"
    using h2 local.face_func by force
  have "\<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> y) = \<partial> i tt (\<Gamma> i ff x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt y"
    using h1 local.face_func by simp
  hence h4: "\<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> y) = \<partial> (i + 1) tt x \<otimes>\<^bsub>(i + 1)\<^esub> y"
    by (metis (full_types) assms(1) assms(2) icid.st_eq1 local.conn_face4)
  thus ?thesis
    by (metis h3 assms(2) assms(3) local.conn_face1 local.conn_face2 local.face_comm_var local.icid.stopp.Dst local.locality)
qed

lemma conn_corner2_var: "\<Gamma>\<Gamma> i ff (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) \<star>\<^bsub>i\<^esub> (\<sigma> i (\<partial> i \<beta> y) \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y))"
proof (cases "DD (i + 1) (\<partial> i \<alpha> x) (\<partial> i \<beta> y)")
  case True
  have h1: "DD (i + 1) (\<Gamma> i ff (\<partial> i \<alpha> x)) (\<partial> i \<beta> y)"
    by (metis True insertCI local.conn_zigzag1_var local.iDst local.icid.ts_msg.src_comp_aux local.locality)
  have h2: "DD (i + 1) (\<sigma> i (\<partial> i \<beta> y)) (\<Gamma> i ff (\<partial> i \<beta> y))"
    by (metis local.conn_face2 local.face_compat_var local.locality)
  have h3: "DD i (\<Gamma> i ff (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) (\<sigma> i (\<partial> i \<beta> y) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y))"
    using True local.conn_corner2_DD by simp
  have "\<Gamma>\<Gamma> i ff (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = {\<Gamma> i ff (\<partial> i \<alpha> x \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y)}"
    by (metis (full_types) True local.icat.pcomp_def_var4 image_empty image_insert) 
  also have "\<dots> = {(\<Gamma> i ff (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> (\<partial> i \<beta> y)) \<otimes>\<^bsub>i\<^esub> (\<sigma> i (\<partial> i \<beta> y) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y))}"
    using True conn_corner2 local.face_compat_var by simp
 also have "\<dots> = {\<Gamma> i ff (\<partial> i \<alpha> x) \<otimes>\<^bsub>(i + 1)\<^esub> (\<partial> i \<beta> y)} \<star>\<^bsub>i\<^esub> {\<sigma> i (\<partial> i \<beta> y) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y)}"
   using h3 local.icat.pcomp_def_var4 local.icid.stopp.conv_atom by simp
  also have "\<dots> = (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> (\<partial> i \<beta> y)) \<star>\<^bsub>i\<^esub> {\<sigma> i (\<partial> i \<beta> y) \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y)}"
    by (metis h1 local.icat.functionality_lem_var local.icat.pcomp_def local.icat.sscatml.r0_absorb local.it_absorb)
  also have "\<dots> = (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>(i + 1)\<^esub> (\<partial> i \<beta> y)) \<star>\<^bsub>i\<^esub> (\<sigma> i (\<partial> i \<beta> y) \<odot>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff (\<partial> i \<beta> y))"
    using h2 local.icat.pcomp_def_var4 by simp
  finally show ?thesis.
next
  case False
  thus ?thesis
    by (metis UN_empty add_eq_self_zero empty_is_image local.conn_face1 local.face_compat_var local.pcomp_face_func_DD multimagma.conv_def nat_neq_iff zero_less_one)
qed

lemma conn_corner2_lift:
  assumes "FFx i X"
  and "FFx i Y"
  shows "\<Gamma>\<Gamma> i ff (X \<star>\<^bsub>(i + 1)\<^esub> Y) = (\<Gamma>\<Gamma> i ff X \<star>\<^bsub>(i + 1)\<^esub> Y) \<star>\<^bsub>i\<^esub> (\<sigma>\<sigma> i Y \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i ff Y)"
proof-
  have h1 :"\<forall>x \<in> X. \<forall>ya \<in> Y. \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<longrightarrow> \<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) = \<partial> i tt (\<Gamma> i ff x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt ya"
    by (metis local.face_func add.commute add_diff_cancel_right' assms(1) bot_nat_0.extremum_unique cancel_comm_monoid_add_class.diff_cancel conn_zigzag1_var empty_not_insert ex_in_conv icat.st_local local.icid.ts_msg.src_comp_aux not_one_le_zero singletonD)
  have h2 :"\<forall>yb \<in> Y. DD (i + 1) (\<sigma> i yb) (\<Gamma> i ff yb) \<longrightarrow> \<partial> i ff (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb) = \<partial> i ff (\<sigma> i yb) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i ff yb)"
    by (simp add: local.face_func)
  have h3: "\<forall>x \<in> X. \<forall>y \<in> Y. DD (i + 1) x y \<longrightarrow> (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> y) \<otimes>\<^bsub>i\<^esub> (\<sigma> i y \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff y) = \<Gamma> i ff (x \<otimes>\<^bsub>(i + 1)\<^esub> y)"
    using assms local.conn_corner2 by simp
  have h4: "\<forall>x \<in> X. \<forall>ya \<in> Y. (\<partial> (i + 1) tt (\<Gamma> i ff x) = \<partial> (i + 1) ff ya) = (\<partial> (i + 1) tt x = \<partial> (i + 1) ff ya)"
    by (metis assms(1) conn_zigzag1_var local.icid.ts_msg.src_comp_aux singletonI)
  have h5: "\<forall>yb \<in> Y. \<forall>yc \<in> Y. (\<partial> (i + 1) tt (\<sigma> i yb) = \<partial> (i + 1) ff (\<Gamma> i ff yc)) = (yb = yc)"
    by (metis assms(2) local.conn_face2 local.inv_sym_sym local.sym_face3_simp)
  have h6: "\<forall>x \<in> X. \<forall>ya \<in> Y. \<forall>yb \<in> Y. (x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> \<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) = \<partial> i ff (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb)) = (x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> \<partial> i tt (\<Gamma> i ff x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt ya = \<partial> i ff (\<sigma> i yb) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i ff yb))"
    using h1 h2 h5 icat.st_local by force
  have "(\<Gamma>\<Gamma> i ff X \<star>\<^bsub>(i + 1)\<^esub> Y) \<star>\<^bsub>i\<^esub> (\<sigma>\<sigma> i Y \<star>\<^bsub>(i + 1)\<^esub> \<Gamma>\<Gamma> i ff Y) = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yc) | x ya yb yc. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> yc \<in> Y \<and> DD (i + 1) (\<Gamma> i ff x) ya \<and> DD (i + 1) (\<sigma> i yb) (\<Gamma> i ff yc) \<and> DD i (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yc)}"
    unfolding local.iconv_prop by fastforce
  also have "\<dots> = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yc) | x ya yb yc. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> yc \<in> Y \<and> \<partial> (i + 1) tt (\<Gamma> i ff x) = \<partial> (i + 1) ff ya \<and> \<partial> (i + 1) tt (\<sigma> i yb) = \<partial> (i + 1) ff (\<Gamma> i ff yc) \<and> \<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) = \<partial> i ff (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yc)}"
    using icat.st_local by simp
  also have "\<dots> = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb) | x ya yb. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> \<partial> i tt (\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) = \<partial> i ff (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb)}"
    using h4 h5 by (smt (verit, del_insts) Collect_cong)
  also have "\<dots> = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb) | x ya yb. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> \<partial> i tt (\<Gamma> i ff x) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i tt ya = \<partial> i ff (\<sigma> i yb) \<otimes>\<^bsub>(i + 1)\<^esub> \<partial> i ff (\<Gamma> i ff yb)}"
    using h6 by fastforce
  also have "\<dots> = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb) | x ya yb. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> \<partial> (i + 1) tt x \<otimes>\<^bsub>(i + 1)\<^esub> ya = \<partial> (i + 1) ff yb \<otimes>\<^bsub>(i + 1)\<^esub> yb}"
    by (smt (z3) Collect_cong assms(1) assms(2) icid.st_eq1 local.conn_face1 local.conn_face4 local.conn_face2 local.face_comm_var)
  also have "\<dots> = {(\<Gamma> i ff x \<otimes>\<^bsub>(i + 1)\<^esub> ya) \<otimes>\<^bsub>i\<^esub> (\<sigma> i yb \<otimes>\<^bsub>(i + 1)\<^esub> \<Gamma> i ff yb) | x ya yb. x \<in> X \<and> ya \<in> Y \<and> yb \<in> Y \<and> \<partial> (i + 1) tt x = \<partial> (i + 1) ff ya \<and> ya = yb}"
    by force
  also have "\<dots> = {\<Gamma> i ff (x \<otimes>\<^bsub>(i + 1)\<^esub> y) | x y. x \<in> X \<and> y \<in> Y \<and> DD (i + 1) x y}"
    by (smt (verit, ccfv_threshold) h3 Collect_cong icat.st_local)
  also have "\<dots> = \<Gamma>\<Gamma> i ff (X \<star>\<^bsub>(i + 1)\<^esub> Y)"
    unfolding local.iconv_prop by force
  finally show ?thesis
    by simp
qed

lemma conn_corner3_var: 
  assumes "j \<noteq> i \<and> j \<noteq> i + 1"
  shows "\<Gamma>\<Gamma> i \<alpha> (\<partial> i \<beta> x \<odot>\<^bsub>j\<^esub> \<partial> i \<gamma> y) = \<Gamma> i \<alpha> (\<partial> i \<beta> x) \<odot>\<^bsub>j\<^esub> \<Gamma> i \<alpha> (\<partial> i \<gamma> y)"
  by (smt (z3) assms empty_is_image image_insert local.conn_corner3 local.conn_face1 local.conn_face3 local.face_compat_var local.iDst local.icat.pcomp_def_var4 local.locality local.pcomp_face_func_DD)

lemma conn_corner3_lift:
  assumes "j \<noteq> i"
  and "j \<noteq> i + 1"
  and "FFx i X"
  and "FFx i Y"
  shows "\<Gamma>\<Gamma> i \<alpha> (X \<star>\<^bsub>j\<^esub> Y) = \<Gamma>\<Gamma> i \<alpha> X \<star>\<^bsub>j\<^esub> \<Gamma>\<Gamma> i \<alpha> Y"
proof-
  have h1: "\<forall>x \<in> X. \<forall>y \<in> Y. DD j (\<Gamma> i \<alpha> x) (\<Gamma> i \<alpha> y) = DD j x y"
    by (metis assms icat.st_local local.conn_face1 local.conn_face3 local.face_comm_var)
  have "\<Gamma>\<Gamma> i \<alpha> X \<star>\<^bsub>j\<^esub> \<Gamma>\<Gamma> i \<alpha> Y = {\<Gamma> i \<alpha> x \<otimes>\<^bsub>j\<^esub> \<Gamma> i \<alpha> y | x y. x \<in> X \<and> y \<in> Y \<and> DD j (\<Gamma> i \<alpha> x) (\<Gamma> i \<alpha> y)}"
    unfolding local.iconv_prop by force
  also have "\<dots> = {\<Gamma> i \<alpha> x \<otimes>\<^bsub>j\<^esub> \<Gamma> i \<alpha> y | x y. x \<in> X \<and> y \<in> Y \<and> DD j x y}"
    using h1 by force
  also have "\<dots> = {\<Gamma> i \<alpha> (x \<otimes>\<^bsub>j\<^esub> y) | x y. x \<in> X \<and> y \<in> Y \<and> DD j x y}"
    using conn_corner3 assms by fastforce
  also have "\<dots> = \<Gamma>\<Gamma> i \<alpha> (X \<star>\<^bsub>j\<^esub> Y)"
    unfolding local.iconv_prop by force
  finally show ?thesis
    by simp
qed

lemma conn_face5 [simp]: "\<partial> (j + 1) \<alpha> (\<Gamma> j (\<not>\<alpha>) (\<partial> j \<gamma> x)) = \<partial> (j + 1) \<alpha> (\<partial> j \<gamma> x)"
  by (smt (verit, ccfv_SIG) icid.s_absorb_var local.conn_corner1_lift_aux local.conn_zigzag1_var local.face_compat_var local.icid.ts_msg.src_comp_cond local.is_absorb singleton_insert_inj_eq')

lemma conn_inv_sym_braid:
  assumes "diffSup i j 2"
  shows "\<Gamma> i \<alpha> (\<theta> j (\<partial> i \<beta> (\<partial> (j + 1) \<gamma> x))) = \<theta> j (\<Gamma> i \<alpha> (\<partial> i \<beta> (\<partial> (j + 1) \<gamma> x)))"
  by (smt (z3) add_diff_cancel_left' assms diff_add_0 diff_is_0_eq' local.conn_face3 local.conn_sym_braid local.face_comm_var local.face_compat_var local.inv_sym_face2 local.inv_sym_sym_var1 local.inv_sym_type_var local.sym_inv_sym nat_1_add_1 nle_le rel_simps(28))

lemma conn_corner4: "\<Gamma>\<Gamma> i tt (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = (\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<partial> i \<alpha> x) \<star>\<^bsub>(i + 1)\<^esub> (\<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<Gamma> i tt (\<partial> i \<beta> y))"
proof (cases "DD (i + 1) (\<partial> i \<alpha> x) (\<partial> i \<beta> y)")
  case True
  have h1: "\<partial>\<partial> (i+1) tt (\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<partial> i \<alpha> x) = {\<sigma> i (\<partial> i \<alpha> x)}"
    by (metis image_empty image_insert local.conn_face1 local.conn_face2 local.face_compat_var local.it_absorb)
  have h2: "\<partial> (i+1) tt (\<partial> i \<alpha> x) = \<partial> (i+1) ff (\<partial> i \<beta> y)"
    using True local.iDst by simp
  hence h3: "\<partial>\<partial> (i+1) ff (\<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<Gamma> i tt (\<partial> i \<beta> y)) = {\<sigma> i (\<partial> i \<alpha> x)}"
    by (smt (z3) add_cancel_right_right conn_face5 dual_order.eq_iff empty_is_image local.comp_face_func local.conn_face4 local.conn_face2 local.face_comm_var local.face_compat_var local.icat.sts_msg.st_local local.it_absorb not_one_le_zero subset_singletonD)
  hence h4: "\<partial>\<partial> (i+1) tt (\<Gamma> i tt (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<partial> i \<alpha> x) \<inter> \<partial>\<partial> (i+1) ff (\<sigma> i (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<Gamma> i tt (\<partial> i \<beta> y)) \<noteq> {}"
    using h1 by simp
  thus ?thesis
    by (smt (z3) True add_cancel_right_right dual_order.eq_iff empty_is_image h1 h3 icat.locality_lifting local.conn_corner1_var local.icat.pcomp_def_var4 local.interchange_var multimagma.conv_atom not_one_le_zero)
next
  case False
  thus ?thesis
    by (smt (z3) Union_empty add_eq_self_zero dual_order.eq_iff icat.st_local image_empty local.conn_face4 local.conn_face2 local.face_comm_var local.face_compat_var multimagma.conv_distl not_one_le_zero)
qed

lemma conn_corner5: "\<Gamma>\<Gamma> i ff (\<partial> i \<alpha> x \<odot>\<^bsub>(i + 1)\<^esub> \<partial> i \<beta> y) = (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y)) \<star>\<^bsub>(i + 1)\<^esub> (\<partial> i \<beta> y \<odot>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<beta> y))"
proof (cases "DD (i + 1) (\<partial> i \<alpha> x) (\<partial> i \<beta> y)")
  case True
  have h1: "\<partial>\<partial> (i+1) ff (\<partial> i \<beta> y \<odot>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<beta> y)) = {\<sigma> i (\<partial> i \<beta> y)}"
    by (metis image_empty image_insert local.conn_face1 local.conn_face2 local.face_compat_var local.is_absorb)
  have h2: "\<partial> (i+1) tt (\<partial> i \<alpha> x) = \<partial> (i+1) ff (\<partial> i \<beta> y)"
    using True local.iDst by simp
  hence h3: "\<partial>\<partial> (i+1) tt (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y)) = {\<sigma> i (\<partial> i \<beta> y)}"
    by (smt (verit, best) add_eq_self_zero conn_face5 dual_order.eq_iff icat.tgt_local image_is_empty local.comp_face_func local.conn_face4 local.face_compat_var local.icat.sts_msg.tgt_local local.icid.stopp.locality local.is_absorb local.sym_face3 local.sym_face1_var1 local.sym_fix_var1 not_one_le_zero subset_singletonD)
  hence h4: "\<partial>\<partial> (i+1) ff (\<partial> i \<beta> y \<odot>\<^bsub>i\<^esub> \<Gamma> i ff (\<partial> i \<beta> y)) \<inter> \<partial>\<partial> (i+1) tt (\<Gamma> i ff (\<partial> i \<alpha> x) \<odot>\<^bsub>i\<^esub> \<sigma> i (\<partial> i \<beta> y)) \<noteq> {}"
    using h1 by simp
  thus ?thesis
    by (smt (z3) True add_cancel_right_right dual_order.eq_iff empty_is_image h1 h3 h4 icat.locality_lifting local.conn_corner2_var local.icat.functionality_lem_var local.interchange_var multimagma.conv_atom not_one_le_zero)
next
  case False
  thus ?thesis
    by (smt (z3) UN_empty add_cancel_right_right dual_order.eq_iff image_empty local.conn_face2 local.face_compat_var local.pcomp_face_func_DD local.sym_func2_DD local.sym_type_var multimagma.conv_def not_one_le_zero)
qed

lemma conn_corner3_alt: "j \<noteq> i \<Longrightarrow>  j \<noteq> i + 1 \<Longrightarrow> \<Gamma>\<Gamma> i \<alpha> (\<partial> i \<beta> x \<odot>\<^bsub>j\<^esub> \<partial> i \<gamma> y) = \<Gamma> i \<alpha> (\<partial> i \<beta> x) \<odot>\<^bsub>j\<^esub> \<Gamma> i \<alpha> (\<partial> i \<gamma> y)"
  by (simp add: local.conn_corner3_var)

lemma conn_shift2:
  assumes "fFx i x"
  and "fFx (i + 2) x"
  shows "\<theta> i (\<theta> (i + 1) (\<Gamma> i \<alpha> x)) = \<Gamma> (i + 1) \<alpha> (\<theta> (i + 1) x)"
proof-
  have "(\<theta> i (\<theta> (i + 1) (\<Gamma> i \<alpha> x)) = \<Gamma> (i + 1) \<alpha> (\<theta> (i + 1) x)) = (\<Gamma> i \<alpha> x = \<sigma> (i + 1) (\<sigma> i (\<Gamma> (i + 1) \<alpha> (\<theta> (i + 1) x))))"
    by (smt (z3) ab_semigroup_add_class.add_ac(1) add_eq_self_zero add_is_0 arith_special(3) assms(1) assms(2) local.conn_face3 local.inv_sym_face2 local.inv_sym_sym local.inv_sym_type_var local.sym_inv_sym local.sym_type_var zero_neq_one)
  also have "\<dots> = True"
    using assms(1) assms(2) local.conn_shift local.inv_sym_face2 local.inv_sym_type_var local.sym_inv_sym by force
  finally show ?thesis
    by simp
qed

end


subsection \<open>Cubical $(\omega,0)$-categories with connections\<close>

text \<open>First we define ri-shell-invertibility.\<close>

abbreviation (in cubical_omega_category_connections) "some_ri_inv i x y \<equiv> (DD i x y \<and> DD i y x \<and> x \<otimes>\<^bsub>i\<^esub> y = \<partial> i ff x \<and> y \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x)"

abbreviation (in cubical_omega_category_connections) "ex_ri_inv i x \<equiv> (\<exists>y. some_ri_inv i x y)"

abbreviation (in cubical_omega_category_connections) "ex_ri_inv_shell k i x \<equiv> (\<forall>j \<alpha>. j + 1 \<le> k \<and> j \<noteq> i \<longrightarrow> ex_ri_inv i (\<partial> j \<alpha> x))"

text \<open>Next we define the class of cubical $(\omega,0)$-categories with connections.\<close>

class cubical_omega_zero_category_connections = cubical_omega_category_connections +
  assumes ri_inv: "k \<ge> 1 \<Longrightarrow> i \<le> k - 1 \<Longrightarrow> dim_bound k x \<Longrightarrow> ex_ri_inv_shell k i x \<Longrightarrow> ex_ri_inv i x"

begin

text \<open>Finally, to show our axiomatisation at work we prove Proposition 2.4.7 from our companion paper, namely that every
cell in an $(\omega,0)$-category is ri-invertible for each natural number i. This requires some background theory engineering.\<close>

lemma ri_inv_fix:
  assumes "fFx i x"
  shows "ex_ri_inv i x"
  by (metis assms icat.st_local local.face_compat_var local.icat.sscatml.l0_absorb)

lemma ri_inv2:
  assumes "k \<ge> 1"
  assumes "dim_bound k x"
  and "ex_ri_inv_shell k i x"
  shows "ex_ri_inv i x"
  proof (cases "i \<le> k - 1")
  case True
  thus ?thesis
    using assms local.ri_inv by simp
next
  case False
  hence "fFx i x"
    using assms(2) by fastforce
  thus ?thesis
    using ri_inv_fix by simp
qed

lemma ri_inv3: 
  assumes "dim_bound k x"
  and "ex_ri_inv_shell k i x"
  shows "ex_ri_inv i x"
proof (cases "k = 0")
  case True
  thus ?thesis
    using assms(1) less_eq_nat.simps(1) ri_inv_fix by simp
next
  case False
  hence "k \<ge> 1"
    by simp
  thus ?thesis
    using assms ri_inv2 by simp
qed

lemma ri_unique: "ex_ri_inv i x = (\<exists>!y. DD i x y \<and> DD i y x \<and> x \<otimes>\<^bsub>i\<^esub> y = \<partial> i ff x \<and> y \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x)"
  by (metis local.icat.pcomp_assoc local.icat.sscatml.assoc_defined local.icat.sscatml.l0_absorb local.icat.sts_msg.st_local local.pcomp_uface)

lemma ri_unique_var: "some_ri_inv i x y \<Longrightarrow> some_ri_inv i x z \<Longrightarrow> y = z"
  using ri_unique by fastforce

definition "ri i x = (THE y. DD i x y \<and> DD i y x \<and> x \<otimes>\<^bsub>i\<^esub> y = \<partial> i ff x \<and> y \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x)"

lemma ri_def_prop:
  assumes "dim_bound k x"
  and "ex_ri_inv_shell k i x"
shows "DD i x (ri i x) \<and> DD i (ri i x) x \<and> x \<otimes>\<^bsub>i\<^esub> (ri i x) = \<partial> i ff x \<and> (ri i x) \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x"
proof-
  have "ex_ri_inv i x"
    using assms ri_inv3 by blast
  hence "\<exists>!y. DD i x y \<and> DD i y x \<and> x \<otimes>\<^bsub>i\<^esub> y = \<partial> i ff x \<and> y \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x"
    by (simp add: ri_unique)
  hence "DD i x (ri i x) \<and> DD i (ri i x) x \<and> x \<otimes>\<^bsub>i\<^esub> (ri i x) = \<partial> i ff x \<and> (ri i x) \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x"
    unfolding ri_def by (smt (verit, del_insts) theI')
  thus ?thesis
    by simp
qed

lemma ri_right:
  assumes "dim_bound k x"
  and "ex_ri_inv_shell k i x"
  shows "x \<otimes>\<^bsub>i\<^esub> ri i x = \<partial> i ff x"
  using assms ri_def_prop by simp

lemma ri_right_set:
  assumes "dim_bound k x"
  and "ex_ri_inv_shell k i x"
  shows "x \<odot>\<^bsub>i\<^esub> ri i x = {\<partial> i ff x}"
  using assms local.icat.pcomp_def_var3 ri_def_prop by blast

lemma ri_left:
  assumes "dim_bound k x"
  and "ex_ri_inv_shell k i x"
  shows "ri i x \<otimes>\<^bsub>i\<^esub> x = \<partial> i tt x"
  using assms ri_def_prop by simp

lemma ri_left_set:
  assumes "dim_bound k x"
  and "ex_ri_inv_shell k i x"
  shows "ri i x \<odot>\<^bsub>i\<^esub> x = {\<partial> i tt x}"
  using assms local.icat.pcomp_def_var3 ri_def_prop by blast

lemma dim_face: "dim_bound k x \<Longrightarrow> dim_bound k (\<partial> i \<alpha> x)"
  by (metis local.double_fix_prop local.face_comm_var)

lemma dim_ri_inv:
  assumes "dim_bound k x"
  and "some_ri_inv i x y"
  shows "dim_bound k y"
proof-
  {fix l \<alpha>
  assume ha: "l \<ge> k"
  have h1: "DD i x (\<partial> l \<alpha> y)"
    by (smt (verit, ccfv_threshold) assms ha icat.st_local icid.s_absorb_var3 local.pcomp_face_func_DD)
  have h2: "DD i (\<partial> l \<alpha> y) x"
    by (metis (full_types) assms ha icid.ts_compat local.iDst local.locality local.pcomp_face_func_DD)
  have h3: "\<partial> l \<alpha> (x \<otimes>\<^bsub>i\<^esub> y) = \<partial> i ff (\<partial> l \<alpha> x)"
    by (metis assms ha local.face_comm_var local.face_compat_var)
  have "\<partial> l \<alpha> (x \<otimes>\<^bsub>i\<^esub> y) = \<partial> l \<alpha> x \<otimes>\<^bsub>i\<^esub> \<partial> l \<alpha> y"
    by (metis ha assms(1) assms(2) local.fFx_prop local.face_func local.icat.sscatml.r0_absorb local.pcomp_uface)
  hence h4: "\<partial> l \<alpha> (x \<otimes>\<^bsub>i\<^esub> y) = x \<otimes>\<^bsub>i\<^esub> \<partial> l \<alpha> y"
    by (metis assms(1) ha local.face_compat_var)
  have "\<partial> l \<alpha> (y \<otimes>\<^bsub>i\<^esub> x) = \<partial> l \<alpha> y \<otimes>\<^bsub>i\<^esub> \<partial> l \<alpha> x"
    by (metis ha assms(1) assms(2) local.fFx_prop local.face_func local.icat.sscatml.r0_absorb local.pcomp_uface)
  hence h5: "\<partial> l \<alpha> (y \<otimes>\<^bsub>i\<^esub> x) = \<partial> l \<alpha> y \<otimes>\<^bsub>i\<^esub> x"
    by (metis assms(1) ha local.face_compat_var)
  have "some_ri_inv i x (\<partial> l \<alpha> y)"
    by (smt (z3) assms(1) assms(2) h1 h2 h4 h5 ha icid.ts_compat local.face_comm_var)
  hence "\<partial> l \<alpha> y = y"
    using ri_unique_var assms(2) by blast}
  thus ?thesis
    by simp
qed

lemma every_dim_k_ri_inv: "dim_bound k x \<Longrightarrow> \<forall>i. ex_ri_inv i x"
proof (induct k arbitrary: x)
  case 0
  thus ?case 
    using ri_inv_fix by simp
next
  case (Suc k)
  {fix i
    have "ex_ri_inv i x"
    proof (cases "i \<ge> Suc k")
      case True 
      thus ?thesis
        using Suc.prems ri_inv_fix by simp
    next
      case False
      {fix j \<alpha>
        assume h: "j \<le> k \<and> j \<noteq> i"
        hence a: "dim_bound k (\<Sigma> j (k - j) (\<partial> j \<alpha> x))"
          by (smt (z3) Suc.prems antisym_conv2 le_add_diff_inverse local.face_comm_var local.face_compat_var local.symcomp_face2 local.symcomp_type_var nle_le not_less_eq_eq)
        have "ex_ri_inv i (\<partial> j \<alpha> x)"
        proof (cases "j < i")
          case True
          obtain y where b: "some_ri_inv (i - 1) (\<Sigma> j (k - j) (\<partial> j \<alpha> x)) y"
            using Suc.hyps a by force
          have c: "dim_bound k y"
            apply (rule_tac x = "\<Sigma> j (k - j) (\<partial> j \<alpha> x)" in dim_ri_inv)
           using a b by simp_all
          hence d: "DD i (\<partial> j \<alpha> x) (\<Theta> j (k - j) y)"
            by (smt (verit) False True a b dual_order.refl h icid.ts_compat le_add_diff_inverse local.iDst local.icid.stopp.ts_compat local.inv_symcomp_face1 local.inv_symcomp_symcomp local.locality not_less_eq_eq)
          hence e: "DD i (\<Theta> j (k - j) y) (\<partial> j \<alpha> x)"
            by (smt (verit) False True b c dual_order.refl h icid.ts_compat le_add_diff_inverse local.iDst local.icid.stopp.ts_compat local.inv_symcomp_face1 local.inv_symcomp_symcomp local.locality local.symcomp_type_var not_less_eq_eq)
          have "\<partial> j \<alpha> x \<otimes>\<^bsub>i\<^esub> \<Theta> j (k - j) y = \<Theta> j (k - j) (\<Sigma> j (k - j) (\<partial> j \<alpha> x) \<otimes>\<^bsub>(i - 1)\<^esub> y)"
            apply (subst inv_symcomp_comp4)
            using True local.symcomp_type_var1 c False One_nat_def b local.face_compat_var local.inv_symcomp_symcomp a by auto
          hence f: "\<partial> j \<alpha> x \<otimes>\<^bsub>i\<^esub> \<Theta> j (k - j) y = \<partial> i ff (\<partial> j \<alpha> x)"
            by (metis False True b h le_add_diff_inverse local.face_compat_var local.inv_symcomp_face1 local.inv_symcomp_symcomp local.symcomp_type_var not_less_eq_eq)
          have "\<Theta> j (k - j) y \<otimes>\<^bsub>i\<^esub> \<partial> j \<alpha> x = \<Theta> j (k - j) (y \<otimes>\<^bsub>(i - 1)\<^esub> \<Sigma> j (k - j) (\<partial> j \<alpha> x))"
            apply (subst inv_symcomp_comp4)
            using True local.symcomp_type_var1 b c False local.face_compat_var local.inv_symcomp_symcomp a by simp_all
          thus ?thesis
            by (metis False True b c d dual_order.refl e f h le_add_diff_inverse local.icid.stopp.Dst local.inv_symcomp_face1 not_less_eq_eq)
        next
          case False
          obtain y where b: "some_ri_inv i (\<Sigma> j (k - j) (\<partial> j \<alpha> x)) y"
            using Suc.hyps a by presburger
          have c: "dim_bound k y"
            apply (rule_tac x = "\<Sigma> j (k - j) (\<partial> j \<alpha> x)" in dim_ri_inv)
            using a b by simp_all
          hence d: "DD i (\<partial> j \<alpha> x) (\<Theta> j (k - j) y)"
            by (smt (verit) False a b dual_order.refl h icid.ts_compat le_add_diff_inverse linorder_neqE_nat local.iDst local.icid.stopp.ts_compat local.inv_symcomp_face2 local.inv_symcomp_symcomp local.locality)
          hence e: "DD i (\<Theta> j (k - j) y) (\<partial> j \<alpha> x)"
            by (smt (z3) False add.commute b c dual_order.refl h le_add_diff_inverse2 linorder_neqE_nat local.face_comm_var local.face_compat_var local.iDst local.inv_symcomp_face2 local.inv_symcomp_symcomp local.locality local.symcomp_face2)
          have "\<partial> j \<alpha> x \<otimes>\<^bsub>i\<^esub> \<Theta> j (k - j) y = \<Theta> j (k - j) (\<Sigma> j (k - j) (\<partial> j \<alpha> x) \<otimes>\<^bsub>i\<^esub> y)"
            apply (subst inv_symcomp_comp2)
            using False h nat_neq_iff local.symcomp_type_var1 b c a local.face_compat_var local.inv_symcomp_symcomp by simp_all
          hence f: "\<partial> j \<alpha> x \<otimes>\<^bsub>i\<^esub> \<Theta> j (k - j) y = \<partial> i ff (\<partial> j \<alpha> x)"
             by (metis False b h local.face_compat_var local.inv_symcomp_face2 local.inv_symcomp_symcomp local.symcomp_type_var1 nat_neq_iff)
          have "\<Theta> j (k - j) y \<otimes>\<^bsub>i\<^esub> \<partial> j \<alpha> x = \<Theta> j (k - j) (y \<otimes>\<^bsub>i\<^esub> \<Sigma> j (k - j) (\<partial> j \<alpha> x))"
            apply (subst inv_symcomp_comp2)
            using False h a b c local.inv_symcomp_symcomp by simp_all
          thus ?thesis
            by (metis False antisym_conv3 b d e f h local.face_compat_var local.inv_symcomp_face2 local.inv_symcomp_symcomp local.symcomp_type_var1)
        qed}
      thus ?thesis
       apply (rule_tac k = "k + 1" in ri_inv)
        using False apply simp_all
        using Suc.prems by blast
    qed}
  thus ?case
    by blast
qed

text \<open>We can now show that every cell is ri-invertible in every direction i.\<close>

lemma every_ri_inv: "ex_ri_inv i x"
  using every_dim_k_ri_inv local.fin_fix by blast

end

end
