import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25245_aux

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [0, 7]⟩,
        ⟨GateOp.not, [6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [2, 9]⟩,
        ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.and, [1, 12]⟩,
        ⟨GateOp.or, [13, 14]⟩ ]
    output := 15 }

theorem circ_fan : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem circ_size : circ.size ≤ 10 := by decide

theorem circ_eval : ∀ i j : Fin 6,
    circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (50622 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_25245_aux

theorem PEqualNP.Outside.L_meta_25245 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50622 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_25245_aux.circ, PEqualNP.Outside.L_meta_25245_aux.circ_fan,
    PEqualNP.Outside.L_meta_25245_aux.circ_size, PEqualNP.Outside.L_meta_25245_aux.circ_eval⟩
