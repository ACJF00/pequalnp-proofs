import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54773 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843710 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.not, [9]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [6, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
