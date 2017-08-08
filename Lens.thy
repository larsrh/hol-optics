theory Lens
imports Iso
begin

locale lens =
  fixes get :: "'s \<Rightarrow> 'a" and set :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  assumes set_get[simp]: "get (set a s) = a"
  assumes get_set[simp]: "set (get s) s = s"
  assumes set_set[simp]: "set a (set a' s) = set a s"
begin

definition modify :: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's" where
[optics]: "modify f s = set (f (get s)) s"

lemma modify_id[simp]: "modify id = id"
unfolding modify_def[abs_def] id_def by auto

lemma modify_comp[simp]: "modify (f \<circ> g) = modify f \<circ> modify g"
unfolding modify_def[abs_def] comp_def by auto

end

context iso begin

definition set where [optics]: "set a _ = back a"

sublocale lens: lens get set
by unfold_locales (auto simp: set_def)

lemma lens_modify_eq[simp]: "lens.modify = modify"
unfolding lens.modify_def[abs_def] modify_def[abs_def] set_def
by auto

end

locale compose_lens_lens =
  one: lens f g + two: lens h i for f :: "'s \<Rightarrow> 'a" and g and h :: "'a \<Rightarrow> 'b" and i
begin

definition [optics]: "get = h \<circ> f"
definition set where [optics]: "set b s = g (i b (f s)) s"

sublocale lens get set
by unfold_locales (auto simp: get_def set_def)

end

context compose_iso_iso begin

sublocale lens_lens: compose_lens_lens f "iso.set g" h "iso.set i" ..

lemma get_eq[simp]: "lens_lens.get = get"
unfolding lens_lens.get_def get_def ..

lemma set_eq[simp]: "lens_lens.set = set"
unfolding lens_lens.set_def[abs_def] one.set_def two.set_def local.set_def[abs_def]
by (simp add: back_def)

end

end