import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_56651 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2113682 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [0, 13]⟩, ⟨.not, [14]⟩, ⟨.or, [7, 15]⟩], 16⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
