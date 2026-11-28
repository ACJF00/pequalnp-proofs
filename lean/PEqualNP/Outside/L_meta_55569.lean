import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55569 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4361406 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [3, 0]⟩,
    ⟨.or, [3, 2]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.and, [4, 6]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [15, 14]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
