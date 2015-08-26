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
"modify f s = set (f (get s)) s"

lemma modify_id[simp]: "modify id = id"
unfolding modify_def[abs_def] id_def by auto

lemma modify_comp[simp]: "modify (f \<circ> g) = modify f \<circ> modify g"
unfolding modify_def[abs_def] comp_def by auto

end

context iso begin

definition set :: "'a \<Rightarrow> 's \<Rightarrow> 's" where
"set a _ = back a"

sublocale lens!: lens get set
by unfold_locales (auto simp: set_def)

lemma lens_modify_eq[simp]: "lens.modify = modify"
unfolding lens.modify_def[abs_def] modify_def[abs_def] set_def
by auto

end

end