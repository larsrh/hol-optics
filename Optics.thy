theory Optics
imports Optional
begin

locale id_iso begin
  definition "get = id"
  definition "back = id"

  sublocale iso get "back"
  by unfold_locales (simp add: get_def back_def)+
end

locale list_nil_prism begin
  definition "get' = case_list (Some ()) (\<lambda>_ _. None)"
  definition "back = (\<lambda>_. [])"

  sublocale prism get' "back"
  by unfold_locales (auto simp: get'_def back_def split: list.splits)
end

locale list_cons_prism begin
  definition "get' = case_list None (\<lambda>x xs. Some (x, xs))"
  definition "back = (\<lambda>(x, xs). x # xs)"

  sublocale prism get' "back"
  by unfold_locales (auto simp: get'_def back_def split: list.splits)
end

locale list_head_optional begin
  definition "get' = case_list None (\<lambda>x _. Some x)"
  definition set where "set x xs = case_list xs (\<lambda>_ xs. x # xs) xs"

  sublocale optional get' set
  by unfold_locales (auto simp: get'_def set_def split: list.splits)
end

end