theory Optics_Examples
imports Optics
begin

context begin

text \<open>Accessing the second element of a @{type list}\<close>

interpretation l1!: list_tail_optional .
interpretation l2!: list_head_optional .

interpretation l!: compose_optional_optional l1.get' l1.set l2.get' l2.set ..

lemma "l.get' [1, 2, 3] = Some 2"
by eval_optics

lemma "l.get' [1] = None"
by eval_optics

end

end