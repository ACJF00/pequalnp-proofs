import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55124 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197167 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.and, [2, 6]⟩, ⟨.not, [4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.not, [10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
