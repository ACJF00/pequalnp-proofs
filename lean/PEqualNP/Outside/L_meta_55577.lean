import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55577

-- A circuit for the one- and two-point inputs of the stated graph.
private def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.and, [3, 4]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [8, 11]⟩,
    ⟨.or, [6, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_55577

theorem PEqualNP.Outside.L_meta_55577 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4377263 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_55577.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55577.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
