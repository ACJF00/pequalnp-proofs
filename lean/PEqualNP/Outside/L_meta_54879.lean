import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54879 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17337 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.not, [3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.not, [8]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [9, 14]⟩, ⟨.not, [15]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
