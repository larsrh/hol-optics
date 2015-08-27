theory Prism
imports Iso
begin

locale prism =
  fixes get' :: "'s \<Rightarrow> 'a option" and "back" :: "'a \<Rightarrow> 's"
  assumes back_get'[simp]: "get' (back a) = Some a"
  assumes get'_back[simp]: "get' s = Some a \<Longrightarrow> back a = s"
begin

definition modify' :: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's option" where
[optics]: "modify' f s = map_option (back \<circ> f) (get' s)"

definition modify :: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's" where
[optics]: "modify f s = (case get' s of None \<Rightarrow> s | Some a \<Rightarrow> back (f a))"

lemma modify_id[simp]: "modify id = id"
unfolding modify_def[abs_def] id_def by (auto split: option.splits)

lemma modify_comp[simp]: "modify (f \<circ> g) = modify f \<circ> modify g"
unfolding modify_def[abs_def] comp_def by (auto split: option.splits)

end

context iso begin

definition [optics]: "get' = Some \<circ> get"

sublocale prism!: prism get' "back"
by unfold_locales (auto simp: get'_def)

lemma prism_modify_eq[simp]: "prism.modify = modify"
unfolding prism.modify_def[abs_def] modify_def[abs_def]
by (simp add: get'_def)

end

locale compose_prism_prism =
  one: prism f g + two: prism h i for f :: "'s \<Rightarrow> 'a option" and g and h :: "'a \<Rightarrow> 'b option" and i
begin

definition [optics]: "get' s = Option.bind (f s) h"
definition [optics]: "back = g \<circ> i"

sublocale prism get' "back"
proof
  fix s b
  assume "get' s = Some b"
  then obtain a where "f s = Some a" "h a = Some b"
    unfolding get'_def
    by (meson bind_eq_Some_conv)
  thus "back b = s"
    by (auto simp: get'_def back_def)
qed (auto simp: get'_def back_def)

end

context compose_iso_iso begin

sublocale prism_prism!: compose_prism_prism "iso.get' f" g "iso.get' h" i ..

lemma get'_eq[simp]: "prism_prism.get' = get'"
unfolding prism_prism.get'_def[abs_def]
unfolding get'_def one.get'_def two.get'_def
by (auto simp: get_def)

lemma back_eq[simp]: "prism_prism.back = back"
unfolding back_def prism_prism.back_def ..

end

context type_definition begin

definition get' :: "'a \<Rightarrow> 'b option" where
[optics]: "get' a = (if a \<in> A then Some (Abs a) else None)"

definition set :: "'b \<Rightarrow> 'a" where
[optics]: "set = Rep"

sublocale prism!: prism get' set
proof
  fix a
  show "get' (set a) = Some a"
    unfolding set_def get'_def
    using Rep Rep_inverse by auto
next
  fix s a
  assume "get' s = Some a"
  hence "s \<in> A" "a = Abs s"
    unfolding get'_def
    by - (cases "s \<in> A"; auto)+
  thus "set a = s"
    unfolding set_def using Abs_inverse by auto
qed

end

end