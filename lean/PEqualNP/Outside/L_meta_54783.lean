import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54783 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274860975 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [7, 13]⟩, ⟨.not, [14]⟩], 15⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
