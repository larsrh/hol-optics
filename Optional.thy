theory Optional
imports Prism Lens
begin

locale optional =
  fixes get' :: "'s \<Rightarrow> 'a option" and set :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  assumes set_get'[simp]: "get' (set a s) = map_option (\<lambda>_. a) (get' s)"
  assumes get'_set[simp]: "get' s = Some a \<Longrightarrow> set a s = s"
  assumes set_set[simp]: "set a (set a' s) = set a s"
begin

definition modify' :: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's option" where
[optics]: "modify' f s = map_option (\<lambda>a. set (f a) s) (get' s)"

definition modify :: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's" where
[optics]: "modify f s = (case get' s of None \<Rightarrow> s | Some a \<Rightarrow> set (f a) s)"

lemma modify_id[simp]: "modify id = id"
unfolding modify_def[abs_def] id_def by (auto split: option.splits)

lemma modify_comp[simp]: "modify (f \<circ> g) = modify f \<circ> modify g"
unfolding modify_def[abs_def] comp_def by (auto split: option.splits)

end

context lens begin

definition [optics]: "get' = Some \<circ> get"

sublocale optional: optional get' set
by unfold_locales (auto simp: get'_def)

lemma modify_eq[simp]: "optional.modify = modify"
unfolding modify_def[abs_def] optional.modify_def[abs_def]
by (simp add: get'_def)

end

context prism begin

definition set where [optics]: "set a s = (case get' s of None \<Rightarrow> s | Some _ \<Rightarrow> back a)"

sublocale optional: optional get' set
by unfold_locales (auto simp: set_def split: option.splits)

lemma modify_eq[simp]: "optional.modify = modify"
unfolding modify_def[abs_def] optional.modify_def[abs_def] set_def
by (rule ext)+ (auto split: option.splits)

lemma modify'_eq[simp]: "optional.modify' = modify'"
unfolding modify'_def[abs_def] optional.modify'_def[abs_def] set_def comp_def
by (rule ext)+ (auto simp: map_option_case split: option.splits)

end

context iso begin

lemma get'_eq[simp]: "lens.get' = get'"
unfolding get'_def lens.get'_def by simp

lemma set_eq[simp]: "prism.set = set"
unfolding set_def[abs_def] prism.set_def[abs_def]
by (simp add: get'_def)

end

locale compose_optional_optional =
  one: optional f g + two: optional h i for f :: "'s \<Rightarrow> 'a option" and g and h :: "'a \<Rightarrow> 'b option" and i
begin

definition [optics]: "get' s = Option.bind (f s) h"
definition set where [optics]: "set b = one.modify (i b)"

sublocale optional get' set
proof
  fix b s
  assume "get' s = Some b"
  then obtain a where "f s = Some a" "h a = Some b"
    unfolding get'_def
    by (meson bind_eq_Some_conv)
  thus "set b s = s"
    unfolding set_def one.modify_def by simp
next
  fix b s
  show "get' (set b s) = map_option (\<lambda>_. b) (get' s)"
    unfolding get'_def set_def one.modify_def
    by (auto split: option.splits)
next
  fix b b' s
  show "set b (set b' s) = set b s"
    unfolding set_def one.modify_def
    by (auto split: option.splits)
qed

end

context compose_prism_prism begin

sublocale optional_optional: compose_optional_optional f "prism.set f g" h "prism.set h i" ..

lemma get'_eq[simp]: "optional_optional.get' = get'"
unfolding get'_def[abs_def] optional_optional.get'_def[abs_def] ..

lemma set_eq[simp]: "optional_optional.set = set"
unfolding set_def[abs_def] optional_optional.set_def[abs_def] one.optional.modify_def[abs_def]
unfolding get'_def back_def comp_apply
unfolding one.set_def two.set_def
by (rule ext)+ (auto split: option.splits)

lemma modify_eq[simp]: "optional_optional.modify = modify"
unfolding optional_optional.modify_def[abs_def] modify_def[abs_def]
unfolding get'_eq set_eq set_def
by (rule ext)+ (auto split: option.splits)

lemma modify'_eq[simp]: "optional_optional.modify' = modify'"
unfolding optional_optional.modify'_def[abs_def] modify'_def[abs_def]
unfolding set_eq get'_eq set_def
by (rule ext)+ (auto cong: map_option_cong)

end

context compose_lens_lens begin

sublocale optional_optional: compose_optional_optional "lens.get' f" g "lens.get' h" i ..

lemma get'_eq[simp]: "optional_optional.get' = get'"
unfolding get'_def[abs_def] optional_optional.get'_def[abs_def]
unfolding get_def one.get'_def two.get'_def
by auto

lemma set_eq[simp]: "optional_optional.set = set"
unfolding set_def[abs_def] optional_optional.set_def[abs_def]
by (rule ext)+ (simp add: one.modify_def)

lemma modify_eq[simp]: "optional_optional.modify = modify"
unfolding optional_optional.modify_def[abs_def] modify_def[abs_def]
unfolding get'_eq set_eq
unfolding set_def get'_def
by simp

end

end