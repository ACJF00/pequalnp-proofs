import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53779 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4294954 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
