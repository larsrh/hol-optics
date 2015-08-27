theory Optics
imports Optional
begin

locale id_iso
begin
  definition [optics]: "get = id"
  definition [optics]:"back = id"

  sublocale iso get "back"
  by unfold_locales (simp add: get_def back_def)+
end

locale bij_iso =
  fixes f assumes bij[intro]: "bij f"
begin
  definition [optics]:"get = f"
  definition [optics]:"back = inv f"

  sublocale iso get "back"
  unfolding get_def back_def
  by auto
end

locale list_nil_prism
begin
  definition [optics]: "get' = case_list (Some ()) (\<lambda>_ _. None)"
  definition [optics]: "back = (\<lambda>_. [])"

  sublocale prism get' "back"
  by unfold_locales (auto simp: get'_def back_def split: list.splits)
end

locale list_cons_prism
begin
  definition [optics]: "get' = case_list None (\<lambda>x xs. Some (x, xs))"
  definition [optics]: "back = (\<lambda>(x, xs). x # xs)"

  sublocale prism get' "back"
  by unfold_locales (auto simp: get'_def back_def split: list.splits)
end

locale list_head_optional
begin
  definition [optics]: "get' = case_list None (\<lambda>x _. Some x)"
  definition set where [optics]: "set x xs = case_list xs (\<lambda>_ xs. x # xs) xs"

  sublocale optional get' set
  by unfold_locales (auto simp: get'_def set_def split: list.splits)
end

locale list_tail_optional
begin
  definition [optics]: "get' = case_list None (\<lambda>_ xs. Some xs)"
  definition set where [optics]: "set xs ys = case_list ys (\<lambda>x _. x # xs) ys"

  sublocale optional get' set
  by unfold_locales (auto simp: get'_def set_def split: list.splits)
end

locale prod_fst_lens
begin
  definition [optics]: "get = fst"
  fun set where [optics, simp del]: "set a (_, b) = (a, b)"

  sublocale lens get set
  by unfold_locales (auto simp: optics)
end

locale prod_snd_lens
begin
  definition [optics]: "get = snd"
  fun set where [optics, simp del]: "set b (a, _) = (a, b)"

  sublocale lens get set
  by unfold_locales (auto simp: optics)
end

end