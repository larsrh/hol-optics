theory Optics
imports Optional
begin

locale id_iso
begin
  definition [optics_def]: "get = id"
  definition [optics_def]:"back = id"

  sublocale iso get "back"
  by unfold_locales (simp add: get_def back_def)+
end

locale bij_iso =
  fixes f assumes bij[intro]: "bij f"
begin
  definition [optics_def]:"get = f"
  definition [optics_def]:"back = inv f"

  sublocale iso get "back"
  unfolding get_def back_def
  by auto
end

locale list_nil_prism
begin
  definition [optics_def]: "get' = case_list (Some ()) (\<lambda>_ _. None)"
  definition [optics_def]: "back = (\<lambda>_. [])"

  sublocale prism get' "back"
  by unfold_locales (auto simp: get'_def back_def split: list.splits)
end

locale list_cons_prism
begin
  definition [optics_def]: "get' = case_list None (\<lambda>x xs. Some (x, xs))"
  definition [optics_def]: "back = (\<lambda>(x, xs). x # xs)"

  sublocale prism get' "back"
  by unfold_locales (auto simp: get'_def back_def split: list.splits)
end

locale list_head_optional
begin
  definition [optics_def]: "get' = case_list None (\<lambda>x _. Some x)"
  definition set where [optics_def]: "set x xs = case_list xs (\<lambda>_ xs. x # xs) xs"

  sublocale optional get' set
  by unfold_locales (auto simp: get'_def set_def split: list.splits)
end

locale list_tail_optional
begin
  definition [optics_def]: "get' = case_list None (\<lambda>_ xs. Some xs)"
  definition set where [optics_def]: "set xs ys = case_list ys (\<lambda>x _. x # xs) ys"

  sublocale optional get' set
  by unfold_locales (auto simp: get'_def set_def split: list.splits)
end

end