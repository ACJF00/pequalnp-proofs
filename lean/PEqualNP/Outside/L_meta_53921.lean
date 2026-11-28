import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53921

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [4, 6]⟩,
    ⟨GateOp.and, [8, 7]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [10, 8]⟩,
    ⟨GateOp.or, [2, 9]⟩,
    ⟨GateOp.not, [11]⟩,
    ⟨GateOp.and, [12, 13]⟩
  ], 14⟩

theorem witness_fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem witness_eval : ∀ i j : Fin 6,
    witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (52406 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_53921

theorem PEqualNP.Outside.L_meta_53921 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52406 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_53921.witness, PEqualNP.Outside.L_meta_53921.witness_fan, by decide, PEqualNP.Outside.L_meta_53921.witness_eval⟩
