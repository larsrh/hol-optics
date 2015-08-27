theory Basics
imports Main "~~/src/HOL/Eisbach/Eisbach"
begin

named_theorems optics

ML\<open>
fun changed_conv cv ct =
  let
    val thm = cv ct
  in
    if Thm.is_reflexive thm then
      raise CTERM ("reflexive", [ct])
    else
      thm
  end

fun optics_conv ctxt =
  let
    val thms = map mk_meta_eq (Named_Theorems.get ctxt @{named_theorems optics})
  in
    Conv.top_sweep_conv (fn _ => Conv.rewrs_conv thms) ctxt
    |> changed_conv
    |> Conv.repeat_conv
  end
\<close>

method_setup optics = \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (CONVERSION (optics_conv ctxt)))\<close>

method eval_optics = (optics, simp)

end