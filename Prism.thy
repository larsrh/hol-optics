theory Prism
imports Iso
begin

locale prism =
  fixes get' :: "'s \<Rightarrow> 'a option" and "back" :: "'a \<Rightarrow> 's"
  assumes back_get'[simp]: "get' (back a) = Some a"
  assumes get'_back[simp]: "get' s = Some a \<Longrightarrow> back a = s"
begin

definition modify' :: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's option" where
"modify' f s = map_option (back \<circ> f) (get' s)"

definition modify :: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's" where
"modify f s = (case get' s of None \<Rightarrow> s | Some a \<Rightarrow> back (f a))"

lemma modify_id[simp]: "modify id = id"
unfolding modify_def[abs_def] id_def by (auto split: option.splits)

lemma modify_comp[simp]: "modify (f \<circ> g) = modify f \<circ> modify g"
unfolding modify_def[abs_def] comp_def by (auto split: option.splits)

end

context iso begin

definition get' :: "'s \<Rightarrow> 'a option" where
"get' = Some \<circ> get"

sublocale prism!: prism get' "back"
by unfold_locales (auto simp: get'_def)

lemma prism_modify_eq[simp]: "prism.modify = modify"
unfolding prism.modify_def[abs_def] modify_def[abs_def]
by (simp add: get'_def)

end

context type_definition begin

definition get' :: "'a \<Rightarrow> 'b option" where
"get' a = (if a \<in> A then Some (Abs a) else None)"

definition set :: "'b \<Rightarrow> 'a" where
"set = Rep"

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