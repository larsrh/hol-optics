theory Optional
imports Prism Lens
begin

locale optional =
  fixes get' :: "'s \<Rightarrow> 'a option" and set :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  assumes set_get'[simp]: "get' (set a s) = Some a"
  assumes get'_set[simp]: "get' s = Some a \<Longrightarrow> set a s = s"
  assumes set_set[simp]: "set a (set a' s) = set a s"
begin

definition modify' :: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's option" where
"modify' f s = map_option (\<lambda>a. set (f a) s) (get' s)"

definition modify :: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's" where
"modify f s = (case get' s of None \<Rightarrow> s | Some a \<Rightarrow> set (f a) s)"

end

context lens begin

definition get' :: "'s \<Rightarrow> 'a option" where
"get' = Some \<circ> get"

sublocale optional!: optional get' set
by unfold_locales (auto simp: get'_def)

lemma modify_eq[simp]: "optional.modify = modify"
unfolding modify_def[abs_def] optional.modify_def[abs_def]
by (simp add: get'_def)

end

context prism begin

definition set :: "'a \<Rightarrow> 's \<Rightarrow> 's" where
"set a _ = back a"

sublocale optional!: optional get' set
by unfold_locales (auto simp: set_def)

lemma modify_eq[simp]: "optional.modify = modify"
unfolding modify_def[abs_def] optional.modify_def[abs_def] set_def
by simp

lemma modify'_eq[simp]: "optional.modify' = modify'"
unfolding modify'_def[abs_def] optional.modify'_def[abs_def] set_def comp_def
by auto

end

context iso begin

lemma get'_eq[simp]: "lens.get' = get'"
unfolding get'_def lens.get'_def by simp

lemma set_eq[simp]: "prism.set = set"
unfolding set_def[abs_def] prism.set_def[abs_def] by simp

end

end