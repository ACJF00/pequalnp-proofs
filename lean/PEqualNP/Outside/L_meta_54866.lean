import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54866

open PEqualNP.CircuitLowerBounds

-- Wire 7 is the disjunction of inputs 1, 4 and 5. Share it between the
-- edges incident to input 0 and the test that input 2 is a singleton.
private def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩,
    ⟨.or, [7, 0]⟩, ⟨.or, [10, 3]⟩, ⟨.not, [11]⟩, ⟨.and, [2, 12]⟩,
    ⟨.or, [8, 9]⟩, ⟨.or, [14, 13]⟩], 15⟩

end PEqualNP.Outside.L_meta_54866

-- Finite replay follows e44b4bfc89bbff1a6bfc442a069acd637e080af4,
-- lean/PEqualNP/Outside/L_meta_24157.lean, adapted to six inputs and this witness.
theorem PEqualNP.Outside.L_meta_54866 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16946 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_54866.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54866.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
