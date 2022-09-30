section \<open>Relpow Implementation\<close>

theory Relpow_Meta_Impl
  imports "Transitive-Closure.Transitive_Closure_Impl"
begin

fun
  relpow_meta_impl :: "(('a * 'b) list \<Rightarrow> ('a * 'b) list ) \<Rightarrow>
(('a * 'b) list \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a * 'b) list \<Rightarrow> 'c \<Rightarrow> nat \<Rightarrow> 'c"
where
  "relpow_meta_impl succ un memb new have 0 = un new have" |
  "relpow_meta_impl succ un memb new have (Suc m) =
    (if new = [] then have
    else
      let
        maybe = succ new;
        have' = un new have;
        new' = filter (\<lambda>x. \<not> memb (fst x) have') maybe
      in relpow_meta_impl succ un memb new' have' m)"

abbreviation "keys \<equiv> map fst"

definition "valid_metas_set valid_meta as \<equiv> (\<forall>(k, v) \<in> as. valid_meta k v)"

locale relpow_data_structure =
  fixes un :: "('a * 'b) list \<Rightarrow> 'c \<Rightarrow> 'c"
    and set_of :: "'c \<Rightarrow> ('a * 'b) set"
    and memb :: "'a \<Rightarrow> 'c \<Rightarrow> bool"
    and empty :: 'c
    and valid_meta :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes un: "fst ` set_of (un as m) = fst ` (set as \<union> set_of m)"
    and memb: "memb a m \<longleftrightarrow> (a \<in> fst ` (set_of m))"
    and empty: "set_of empty = {}"
    and un_valid_metas: "valid_metas_set valid_meta (set as) \<Longrightarrow> valid_metas_set valid_meta (set_of m)
          \<Longrightarrow> valid_metas_set valid_meta (set_of (un as m))"
begin

abbreviation "valid_metas \<equiv> valid_metas_set valid_meta"

abbreviation "keys_of m \<equiv> fst ` set_of m"

lemma valid_metas_empty: "valid_metas (set_of empty)"
  using valid_metas_set_def empty by auto

end

locale relpow_meta_succ =
  relpow_data_structure un set_of memb empty valid_meta
  for un :: "('a * 'b) list \<Rightarrow> 'c \<Rightarrow> 'c" and set_of memb empty valid_meta +
  fixes succ :: "('a * 'b) list \<Rightarrow> ('a * 'b) list"
    and succ_rel :: "('a * 'a) set"
  assumes succ_rel: "fst ` (set (succ as)) = {b. \<exists>a \<in> fst ` (set as). (a, b) \<in> succ_rel}"
    and succ_valid_metas: "valid_metas_set valid_meta (set as) \<Longrightarrow> valid_metas_set valid_meta (set (succ as))"
begin

abbreviation "add_undef_meta \<equiv> map (\<lambda>a. (a,undefined))"

definition "succ' as \<equiv> keys (succ (add_undef_meta as))"

definition "un' as \<equiv> un (add_undef_meta as)"


sublocale relpow': set_access_succ keys_of memb empty un' succ' succ_rel
  by (unfold_locales,
      auto simp: un memb empty succ_rel succ'_def un'_def,
      force)

definition "eq_new new new' \<equiv> set (keys new) = set new'" 

lemma succ_eq: "eq_new new new' \<Longrightarrow> eq_new (succ new) (succ' new')"
  using succ_rel by (auto simp add: eq_new_def succ'_def) fastforce

lemma un_eq: "eq_new as as' \<Longrightarrow> keys_of bs = keys_of bs'
  \<Longrightarrow> keys_of (un as bs) = keys_of (un' as' bs')"
  using relpow'.un by (auto simp add: eq_new_def un'_def un)

lemma relpow_relpow'_aux: "eq_new new new' \<Longrightarrow> keys_of have = keys_of have'
  \<Longrightarrow> keys_of (relpow_meta_impl succ un memb new have n)
    = keys_of (relpow_impl succ' un' memb new' have' n)"
proof (induction n arbitrary: "have" have' new new')
  case 0
  then show ?case by (simp add: un_eq)
next
  case (Suc n)
  then show ?case
  proof (cases "new = []")
    case True
    then have "new' = []" using Suc.prems(1) by (auto simp: eq_new_def) 
    then show ?thesis using True Suc.prems(2) by simp
  next
    case False
    then have new': "new' \<noteq> []" using Suc.prems(1) by (auto simp: eq_new_def)
    let ?maybe1 = "succ new"
    let ?maybe2 = "succ' new'"
    have maybe_eq: "eq_new ?maybe1 ?maybe2" using Suc.prems(1) by (simp add: succ_eq)
    let ?have1 = "un new have"
    let ?have2 = "un' new' have'"
    have have'_eq: "keys_of ?have1 = keys_of ?have2" using Suc.prems by (auto simp: un_eq)
    let ?new1 = "filter (\<lambda>x. \<not> memb (fst x) ?have1) ?maybe1"
    let ?new2 = "filter (\<lambda>x. \<not> memb x ?have2) ?maybe2"
    have new'_eq: "eq_new ?new1 ?new2" using maybe_eq have'_eq eq_new_def relpow'.memb by (auto simp: eq_new_def)
    show ?thesis using Suc.IH[OF new'_eq have'_eq] False new' by (simp add: Let_def)
  qed
qed

lemma relpow_relpow': "keys_of (relpow_meta_impl succ un memb new have n)
    = keys_of (relpow_impl succ' un' memb (keys new) have n)"
  by (simp add: eq_new_def relpow_relpow'_aux)

theorem trancl_meta_impl: "keys_of (relpow_meta_impl succ un memb new empty n)
      = {b | a b m. a \<in> fst ` set new \<and> m \<le> n \<and> (a, b) \<in> succ_rel ^^ m}"
  by (simp add: relpow_relpow' relpow'.relpow_impl)



lemma relpow_valid_metas_gen: "valid_metas (set_of have) \<Longrightarrow> valid_metas (set new)
  \<Longrightarrow> valid_metas (set_of (relpow_meta_impl succ un memb new have n))"
proof (induction n arbitrary: new "have")
  case 0
  then show ?case by (simp add: un_valid_metas)
next
  case (Suc n)
  let ?have' = "un new have"
  have valid_have': "valid_metas (set_of ?have')" by (simp add: un_valid_metas Suc.prems)
  let ?new' = "filter (\<lambda>x. \<not> memb (fst x) ?have') (succ new)"                                                        
  have "valid_metas (set (succ new))" using succ_valid_metas Suc.prems by auto
  hence valid_new': "valid_metas (set ?new')" using filter_is_subset by (auto simp: valid_metas_set_def)
  then show ?case using Suc.IH Suc valid_have' valid_new' by (simp add: Let_def)
qed

theorem relpow_valid_metas: "valid_metas (set new) \<Longrightarrow> valid_metas (set_of (relpow_meta_impl succ un memb new empty n))"
  using relpow_valid_metas_gen valid_metas_empty by blast

end

end