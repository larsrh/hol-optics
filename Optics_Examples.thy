theory Optics_Examples
imports Optics
begin

context begin

text \<open>Accessing the second element of a @{type list}\<close>

interpretation l1: list_tail_optional .
interpretation l2: list_head_optional .

interpretation l: compose_optional_optional l1.get' l1.set l2.get' l2.set ..

lemma
  "l.get' [1, 2, 3] = Some 2"
  "l.get' [1] = None"
  "l.set 0 [1, 2, 3] = [1, 0, 3]"
  "l.set 0 [1] = [1]"
  "l.modify (op + 1) [1, 2, 3] = [1, 3, 3]"
  "l.modify (op + 1) [1] = [1]"
by eval_optics+

end

context begin

text \<open>The same as above, but this time more convoluted\<close>

interpretation l1: list_cons_prism .
interpretation l2: prod_snd_lens .
interpretation l3: list_head_optional .

interpretation l12: compose_optional_optional l1.get' l1.set l2.get' l2.set ..
interpretation l: compose_optional_optional l12.get' l12.set l3.get' l3.set ..

lemma
  "l.get' [1, 2, 3] = Some 2"
  "l.get' [1] = None"
  "l.set 0 [1, 2, 3] = [1, 0, 3]"
  "l.set 0 [1] = [1]"
  "l.modify (op + 1) [1, 2, 3] = [1, 3, 3]"
  "l.modify (op + 1) [1] = [1]"
by eval_optics+

end

end