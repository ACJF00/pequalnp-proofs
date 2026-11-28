import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54711 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270582944 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 1]⟩, ⟨.or, [3, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [5, 0]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [11, 1]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [13]⟩, ⟨.or, [8, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
