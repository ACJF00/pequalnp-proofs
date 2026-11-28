import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53785

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }], output := 14 }

end PEqualNP.Outside.L_meta_53785

theorem PEqualNP.Outside.L_meta_53785 :
∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101182 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_53785.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53785.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
