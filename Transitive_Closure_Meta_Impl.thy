section \<open>Transitive Closure Implementation\<close>

theory Transitive_Closure_Meta_Impl
  imports "HOL-Library.Mapping" "HOL-Library.Product_Lexorder" Relpow_Meta_Impl
begin

subsection \<open>Data structure\<close>

definition "un_map \<equiv> fold (\<lambda>(u,b). Mapping.update u b)"

definition "memb_map u m \<equiv> \<not> Option.is_none (Mapping.lookup m u)"

lemma un_keys: "Mapping.keys (un_map as m) = fst ` set as \<union> Mapping.keys m"
  by (induction as arbitrary: m) (auto simp: un_map_def)

lemma update_valid_metas: "valid_meta k v \<Longrightarrow> valid_metas_set valid_meta (Mapping.entries m) \<Longrightarrow>
  valid_metas_set valid_meta (Mapping.entries (Mapping.update k v m))"
  unfolding valid_metas_set_def by (simp add: entries_delete entries_update)

lemma un_map_valid_metas:
  assumes "valid_metas_set valid_meta (set as)"
      and "valid_metas_set valid_meta (Mapping.entries m)"
    shows "valid_metas_set valid_meta (Mapping.entries (un_map as m))"
  using assms
  unfolding un_map_def
proof (induction as arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then have as_valid: "valid_metas_set valid_meta (set as)" unfolding valid_metas_set_def by simp
  obtain k v where kv: "a = (k,v)" by fastforce
  then have "valid_meta k v" using Cons(2) unfolding valid_metas_set_def by simp
  then have "valid_metas_set valid_meta (Mapping.entries (Mapping.update k v m))" using update_valid_metas Cons(3) by fast
  then show ?case using kv as_valid Cons update_valid_metas by simp
qed

interpretation trancl_data_structure_mapping: relpow_data_structure un_map Mapping.entries memb_map Mapping.empty
  unfolding memb_map_def
  by (unfold_locales, auto simp: image_Un un_keys keys_is_none_rep un_map_valid_metas)

subsection \<open>Transitive Closure with successor function\<close>

locale trancl_meta_succ =
  relpow_data_structure un set_of memb empty valid_meta
  for un :: "(('a * 'a) * 'b) list \<Rightarrow> 'c \<Rightarrow> 'c"
    and set_of memb empty valid_meta +
  fixes succ :: "(('a * 'a) * 'b) list \<Rightarrow> (('a * 'a) * 'b) list"
    and rel_meta :: "(('a * 'a) * 'b) list"
  assumes succ_rel_step: "fst ` set (succ as) = {(x,z) | x y z. (x,y) \<in> fst ` set as \<and> (y,z) \<in> fst ` set rel_meta}"
      and succ_valid_metas: "valid_metas (set as) \<Longrightarrow> valid_metas (set (succ as))"
begin

definition "rel \<equiv> fst ` set rel_meta"

definition "succ_rel \<equiv> {((x,y),(x,z)) | x y z. (y,z) \<in> rel}"


lemma succ_succ_rel: "fst ` set (succ as) = {b. \<exists>a\<in>fst ` set as. (a, b) \<in> succ_rel}" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r" unfolding succ_rel_def rel_def succ_rel_step by blast
  show "?r \<subseteq> ?l"
  proof
    fix b
    assume "b \<in> ?r"
    then obtain a where a: "a \<in> fst ` set as" and "(a,b) \<in> succ_rel" by blast
    then obtain x y z where "a = (x,y) \<and> b = (x,z) \<and> (y,z) \<in> rel" unfolding succ_rel_def by auto
    then show "b \<in> ?l" unfolding succ_rel_step rel_def using a by auto
  qed
qed


sublocale relpow_meta_succ: relpow_meta_succ un set_of memb empty valid_meta succ succ_rel
  using succ_succ_rel succ_valid_metas by unfold_locales


lemma rel_succ_comp_gen: "{b. \<exists>a. a \<in> as \<and> (a,b) \<in> succ_rel ^^ m} = as O rel ^^ m" (is "?l m = ?r m")
proof
  show "?l m \<subseteq> ?r m"
  proof (induction m)
    case 0
    then show ?case by auto
  next
    case (Suc m)
    show ?case
    proof
      fix b
      assume b_in_l: "b \<in> ?l (Suc m)"
      then obtain a z
        where "a \<in> as"
          and "(a,z) \<in> succ_rel ^^ m"
          and zb: "(z,b) \<in> succ_rel" by auto
      then have "z \<in> as O rel ^^ m" using Suc by blast
      then show "b \<in> ?r (Suc m)" using zb unfolding succ_rel_def by auto
    qed
  qed
next
  show "?r m \<subseteq> ?l m"
  proof (induction m)
    case 0
    then show ?case by auto
  next
    case (Suc m)
    show ?case
    proof
      fix b
      assume "b \<in> ?r (Suc m)"
      then obtain z where y_in_r: "z \<in> ?r m" and "b \<in> {z} O rel" by auto
      then have zb_relpow_rel: "(z, b) \<in> succ_rel" using succ_rel_def by blast
      have "z \<in> ?l m" using y_in_r Suc by auto
      then show "b \<in> ?l (Suc m)" using zb_relpow_rel by auto 
    qed
  qed
qed

lemma rel_succ_comp: "{b. \<exists>a. a \<in> rel \<and> (a,b) \<in> succ_rel ^^ m} = rel ^^ Suc m"
  unfolding rel_succ_comp_gen using relpow_commute by simp

lemma ntrancl_Suc: "ntrancl (Suc n) rel = ntrancl n rel \<union> rel ^^ Suc (Suc n)" (is "?l = ?r")
proof-
  have "{i. 0 < i \<and> i \<le> Suc (Suc n)} = {i. 0 < i \<and> i \<le> Suc n} \<union> {Suc (Suc n)}" by auto
  then have "ntrancl (Suc n) rel = \<Union> ((^^) rel ` ({i. 0 < i \<and> i \<le> Suc n} \<union> {Suc (Suc n)}))" unfolding ntrancl_def by auto
  also have "\<dots> = ntrancl n rel \<union> rel ^^ Suc (Suc n)" unfolding ntrancl_def by auto
  finally show ?thesis .
qed

lemma relpow_impl_ntrancl: "{b. \<exists>a m. a \<in> rel \<and> m \<le> n \<and> (a, b) \<in> succ_rel ^^ m}
    = ntrancl n rel" (is "?l n = ?r n")
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "?l (Suc n) = {b. \<exists>a m. a \<in> rel \<and> (m \<le> n \<or> m = Suc n) \<and> (a, b) \<in> succ_rel ^^ m}" by (simp add: le_Suc_eq)
  then have "?l (Suc n) = ?l n \<union> {b. \<exists>a. a \<in> rel \<and> (a, b) \<in> succ_rel ^^ Suc n}" by force
  also have "\<dots> = ?l n \<union> rel ^^ Suc (Suc n)" using rel_succ_comp by blast
  also have "\<dots> = ntrancl n rel \<union> rel ^^ Suc (Suc n)" using Suc by simp
  also have "\<dots> = ntrancl (Suc n) rel" using ntrancl_Suc by simp
  finally show ?case .
qed

lemma ntrancl_mono: "n \<le> m \<Longrightarrow> ntrancl n rel \<subseteq> ntrancl m rel" unfolding ntrancl_def by force

lemma ntrancl_bounded: "finite r \<Longrightarrow> ntrancl (card r - 1 + n) r = r\<^sup>+"
  by (induction n, simp add: finite_trancl_ntranl, fastforce)

theorem relpow_meta_trancl: "fst ` set_of (relpow_meta_impl succ un memb rel_meta empty (length rel_meta)) = trancl rel"
proof -
  have "ntrancl (length rel_meta) rel = trancl rel"
  proof
    have card_leq: "card rel - 1 \<le> length rel_meta"
      by (metis List.finite_set card_image_le card_length diff_le_self le_trans rel_def)
    have "finite rel" unfolding rel_def by simp
    then have "trancl rel = ntrancl (card rel - 1) rel" by (simp add: finite_trancl_ntranl)
    then show "trancl rel \<subseteq> ntrancl (length rel_meta) rel" using card_leq ntrancl_mono by simp
  next
    show "ntrancl (length rel_meta) rel \<subseteq> trancl rel" using ntrancl_bounded
      by (metis List.finite_set le_add2 list.set_map ntrancl_mono rel_def)
  qed
  then show ?thesis using relpow_meta_succ.trancl_meta_impl rel_def relpow_impl_ntrancl by simp
qed

end


fun to_rel_map :: "(('a * 'a) * 'b) list \<Rightarrow> ('a, ('a * 'b) list) mapping" where
  "to_rel_map [] = Mapping.empty"
| "to_rel_map (((x,y),b)#xs) = (let m = to_rel_map xs in
    Mapping.update x ((y,b) # Mapping.lookup_default [] m x) m)"

fun succ_map :: "('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, ('a * 'b) list) mapping \<Rightarrow> (('a * 'a) * 'b) list \<Rightarrow> (('a * 'a) * 'b) list" where
  "succ_map combine_meta rel_map [] = []"
| "succ_map combine_meta rel_map (((x,y),b)#xs) = 
    map (\<lambda>(z,b'). ((x,z), combine_meta b b')) (Mapping.lookup_default [] rel_map y) @ succ_map combine_meta rel_map xs"

locale trancl_meta_map =
  relpow_data_structure un set_of memb empty valid_meta
  for un :: "(('a::linorder \<times> 'a) \<times> 'b) list \<Rightarrow> 'c \<Rightarrow> 'c"
    and set_of memb empty valid_meta +
  fixes combine_meta :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
    and rel_meta :: "(('a \<times> 'a) \<times> 'b) list"
  assumes combine_meta_valid: "valid_meta (x,y) b1 \<Longrightarrow> valid_meta (y,z) b2 \<Longrightarrow> valid_meta (x,z) (combine_meta b1 b2)"
      and valid_rel_meta: "valid_metas_set valid_meta (set rel_meta)"
begin

abbreviation "succ \<equiv> succ_map combine_meta (to_rel_map rel_meta)"

lemma rel_map_default_lookup: "set (Mapping.lookup_default [] (to_rel_map rel) y) = {(z,b). ((y,z),b) \<in> set rel}"
  by (induction rel) (auto simp: lookup_default_empty lookup_default_update' Let_def split: if_splits)

lemma set_succ: "set (succ as)
  = {((x,z),combine_meta p q) | x y z p q. ((x,y),p) \<in> set as \<and> ((y,z),q) \<in> set rel_meta}" (is "?l as = ?r as")
proof (induction as)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then obtain x y p where a_xyb: "a = ((x,y),p)" by (metis surj_pair)
  then have "?l (a#as) = {((x,z),combine_meta p q) | z q. ((y,z),q) \<in> set rel_meta} \<union> ?l as" using rel_map_default_lookup by fastforce
  also have "\<dots> = ?r (a#as)" using a_xyb Cons by fastforce
  finally show ?case .
qed

lemma succ_rel_meta: "fst ` set (succ as) = {(x,z) | x y z. (x, y) \<in> fst ` set as \<and> (y, z) \<in> fst ` set rel_meta}"
  unfolding set_succ by force

lemma succ_valid_meta:
  assumes valid_as: "valid_metas_set valid_meta (set as)"
    shows "valid_metas_set valid_meta (set (succ as))"
  unfolding valid_metas_set_def
proof
  fix b
  assume "b \<in> set (succ as)"
  then obtain x y z p q
    where "b = ((x,z),combine_meta p q)"
      and "((x,y),p) \<in> set as"
      and "((y,z),q) \<in> set rel_meta" using set_succ by auto
  then show "case b of (u,r) \<Rightarrow> valid_meta u r" using combine_meta_valid valid_rel_meta valid_as by (auto simp: valid_metas_set_def split: prod.splits)
qed

sublocale trancl_meta_succ un set_of memb empty valid_meta succ rel_meta
  by unfold_locales (auto simp: succ_rel_meta succ_valid_meta)

end

locale trancl_meta_rbt =
  fixes combine_meta :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
    and valid_meta :: "(('a::linorder) \<times> 'a) \<Rightarrow> 'b \<Rightarrow> bool"
    and rel_meta :: "(('a \<times> 'a) \<times> 'b) list"
  assumes combine_meta_valid: "valid_meta (x,y) b1 \<Longrightarrow> valid_meta (y,z) b2 \<Longrightarrow> valid_meta (x,z) (combine_meta b1 b2)"
      and valid_rel_meta: "valid_metas_set valid_meta (set rel_meta)"
begin

sublocale trancl_meta_map un_map Mapping.entries memb_map Mapping.empty valid_meta combine_meta rel_meta
  by unfold_locales (auto simp: combine_meta_valid valid_rel_meta)

abbreviation "trancl_meta_impl \<equiv> (relpow_meta_impl succ un_map memb_map rel_meta Mapping.empty (length rel_meta))"

thm relpow_meta_trancl

thm relpow_meta_succ.relpow_valid_metas

end


subsection \<open>Transitive Closure with can\_combine function\<close>

locale relpow_meta_combine =
  relpow_data_structure un set_of memb empty valid_meta
  for un :: "(('a::linorder) * 'b) list \<Rightarrow> 'c \<Rightarrow> 'c" and set_of memb empty valid_meta +
  fixes can_combine :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and combine :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and combine_meta :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
    and as :: "('a \<times> 'b) list"
  assumes valid_meta_combine: "can_combine k1 k2 \<Longrightarrow> valid_meta k1 v1 \<Longrightarrow> valid_meta k2 v2
      \<Longrightarrow> valid_meta (combine k1 k2) (combine_meta k1 v1 k2 v2)"
    and as_valid_metas: "valid_metas (set as)"
begin

fun succ :: "(('a * 'b) list \<Rightarrow> ('a * 'b) list)" where
  "succ [] = []"
| "succ ((a,p)#xs) =
    map (\<lambda>(b,q). (combine a b, combine_meta a p b q)) (filter (\<lambda>(b,q). can_combine a b) as)
    @ succ xs"

definition relpow_meta_combine_impl :: 'c where
  "relpow_meta_combine_impl = relpow_meta_impl succ un memb as empty (length as)"

definition "rel_succ \<equiv> {(a,combine a b) |a b. b \<in> fst ` set as \<and> can_combine a b}"

lemma succ_aux: "set (map (\<lambda>(b,q). (combine a b, combine_meta a p b q)) (filter (\<lambda>(b,q). can_combine a b) as))
    = {(combine a b, combine_meta a p b q) | b q. (b,q) \<in> set as \<and> can_combine a b}" by auto

lemma succ_set: "set (succ xs) = {(combine a b, combine_meta a p b q) |a p b q. (a,p) \<in> set xs \<and> (b,q) \<in> set as \<and> can_combine a b}"
  by (induction xs) (simp,fastforce)

lemma succ_rel_succ: "fst ` set (succ xs) = {b. \<exists>a\<in>fst ` set xs. (a, b) \<in> rel_succ}"
proof -
  have "fst ` set (succ xs) = fst ` {(combine a b, combine_meta a p b q) | a p b q. (a,p) \<in> set xs \<and>(b,q) \<in> set as \<and> can_combine a b}" using succ_set by simp
  also have "\<dots> = {combine a b | a p b q. (a,p) \<in> set xs \<and>(b,q) \<in> set as \<and> can_combine a b}" by force
  also have "\<dots> = {b. \<exists>a\<in>fst ` set xs. (a, b) \<in> rel_succ}" unfolding rel_succ_def by force
  finally show ?thesis .
qed

lemma succ_valid_metas: "valid_metas (set as) \<Longrightarrow> valid_metas (set xs) \<Longrightarrow> valid_metas (set (succ xs))"
  unfolding valid_metas_set_def
  using succ_set valid_meta_combine by (auto split: prod.splits)

sublocale relpow_meta_succ un set_of memb empty valid_meta succ rel_succ
  using succ_rel_succ succ_valid_metas as_valid_metas by unfold_locales

end

locale trancl_meta_combine_impl =
  relpow_data_structure un set_of memb empty valid_meta
  for un :: "(('a::linorder * 'a) * 'b) list \<Rightarrow> 'c \<Rightarrow> 'c" and set_of memb empty valid_meta +
  fixes rel_meta :: "(('a \<times> 'a) \<times> 'b) list"
    and combine_meta :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes rel_valid_metas: "valid_metas (set rel_meta)"
    and valid_meta_combine_meta: "valid_meta (x, y) pxy \<Longrightarrow> valid_meta (y, z) pyz
      \<Longrightarrow> valid_meta (x, z) (combine_meta pxy pyz)"
begin

definition can_combine :: "('a * 'a) \<Rightarrow> ('a * 'a) \<Rightarrow> bool" where
  "can_combine = (\<lambda>(x, y) (y', z). y = y')"

definition combine :: "('a * 'a) \<Rightarrow> ('a * 'a) \<Rightarrow> ('a * 'a)" where 
  "combine = (\<lambda>(x, y) (y', z). (x, z))"

sublocale relpow_meta_combine un set_of memb empty valid_meta can_combine combine "\<lambda>u b1 v b2. combine_meta b1 b2" rel_meta
  by unfold_locales (auto simp: valid_meta_combine_meta combine_def can_combine_def rel_valid_metas)

lemma succ_rel_meta: "fst ` set (succ as) = {(x,z) | x y z. (x,y) \<in> fst ` set as \<and> (y,z) \<in> fst ` set rel_meta}" (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
  proof
    fix c
    assume "c \<in> ?l"
    then obtain a p b q where c: "c = combine a b" and a_as: "(a, p) \<in> set as" and b_rel_meta: "(b, q) \<in> set rel_meta \<and> can_combine a b" using succ_set by auto
    then obtain x y z where a: "a = (x,y)" and b: "b = (y,z)" unfolding can_combine_def by blast
    have fst_set_ab: "a \<in> fst ` set as \<and> b \<in> fst ` set rel_meta" using a_as b_rel_meta by force
    have c_xy: "c = (x,z)" by (simp add: c combine_def a b)
    then show "c \<in> ?r" using fst_set_ab by (auto simp add: a b c combine_def)
  qed
  show "?l \<supseteq> ?r"
  proof
    fix c
    assume "c \<in> ?r"
    then obtain x y z where c: "c = (x,z)" and xy_as: "(x,y) \<in> fst ` set as" and yz_rel_meta: "(y,z) \<in> fst ` set rel_meta" by auto
    then obtain p q where xy_p_as: "((x,y),p) \<in> set as" and yz_q_rel_meta: "((y,z),q) \<in> set rel_meta" by auto
    have c_combine: "c = combine (x,y) (y,z)" by (simp add: c combine_def)
    have can_combine: "can_combine (x,y) (y,z)" by (simp add: can_combine_def)
    then show "c \<in> ?l" unfolding succ_set using xy_p_as yz_q_rel_meta c_combine by force
  qed
qed

sublocale trancl_meta_succ: trancl_meta_succ un set_of memb empty valid_meta succ rel_meta
  by unfold_locales (auto simp add: succ_rel_meta succ_valid_metas rel_valid_metas)

theorem trancl_meta_combine: "keys_of (relpow_meta_impl succ un memb rel_meta empty (length rel_meta)) = trancl_meta_succ.rel\<^sup>+"
  using trancl_meta_succ.relpow_meta_trancl .

end

end