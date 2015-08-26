theory Iso
imports Main
begin

locale iso =
  fixes get :: "'s \<Rightarrow> 'a" and "back" :: "'a \<Rightarrow> 's"
  assumes get_back[simp]: "back (get a) = a" and back_get[simp]: "get (back s) = s"
begin

definition modify :: "('a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 's" where
"modify f s = back (f (get s))"

lemma modify_id[simp]: "modify id = id"
unfolding modify_def[abs_def] id_def by simp

lemma modify_comp[simp]: "modify (f \<circ> g) = modify f \<circ> modify g"
unfolding modify_def[abs_def] comp_def by simp

end

lemma bij_iso[intro]:
  assumes "bij f" shows "iso f (inv f)"
proof
  fix a
  show "inv f (f a) = a"
    using assms unfolding bij_betw_def by (simp add: inv_f_f)
next
  fix s
  show "f (inv f s) = s"
    using assms unfolding bij_betw_def by (simp add: surj_f_inv_f)
qed

lemma rev_iso:
  assumes "iso f g" shows "iso g f"
proof -
  interpret iso f g using assms .
  show ?thesis
    by unfold_locales auto
qed

locale product_iso =
  left: iso f g + right: iso h i for f :: "'s \<Rightarrow> 'a" and g and h :: "'t \<Rightarrow> 'b" and i
begin

fun get :: "'s \<times> 't \<Rightarrow> 'a \<times> 'b" where
"get (s, t) = (f s, h t)"

fun "back" :: "'a \<times> 'b \<Rightarrow> 's \<times> 't" where
"back (a, b) = (g a, i b)"

sublocale iso get "back"
by unfold_locales auto

end

end