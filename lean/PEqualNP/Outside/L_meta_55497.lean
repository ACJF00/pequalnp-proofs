import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55497 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4311483 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [3, 4]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [5, 0]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.not, [14]⟩, ⟨.and, [9, 15]⟩], 16⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
