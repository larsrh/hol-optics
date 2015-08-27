theory Basics
imports Main "~~/src/HOL/Eisbach/Eisbach"
begin

named_theorems optics_basic
named_theorems optics_def

method eval_optics = (simp add: optics_basic, simp add: optics_def)

end