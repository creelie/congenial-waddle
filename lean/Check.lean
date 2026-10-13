import NilFree

/-! The axioms behind the main theorems: the three standard ones (`propext`, `Classical.choice`,
`Quot.sound`) and one axiom per `native_decide` call. Each of these asserts exactly the Boolean
equation that the compiled code evaluated: `NilCore.root () = true` (the search tree closes),
`NilCore.checkCands () = true` (the candidate table is as described). The examples
(`NilFree.mat5_nilFree`, `NilFree.nilFree_C2`, `NilFree.nilFree_C5`) are checked by the kernel, and
the results of `NilFree.Holds` and `NilFree.Char3` use only the three standard axioms. -/

#print axioms NilFree.exists_nilpotent
#print axioms NilFree.not_conjecture8
#print axioms NilFree.exists_nilFree_five
#print axioms NilFree.isGreatest_nilFree_finrank
#print axioms NilFree.not_holdsAt_zmod3
#print axioms NilFree.holdsAt_le_two
#print axioms NilFree.holdsAt_zmod2
#print axioms NilFree.holdsAt_zmod5
#print axioms NilFree.existsUnique_nilpotent_translate
#print axioms NilFree.exists_nilpotent_of_one_mem
#print axioms NilFree.one_not_mem_of_nilFree
#print axioms NilFree.eq_smul_one_of_trace_mul
#print axioms NilFree.c2_eq_trace_sq
#print axioms NilFree.c2_add_smul_one
#print axioms NilFree.det_add_smul_one'
#print axioms NilFree.trace_c2_of_isNilpotent
