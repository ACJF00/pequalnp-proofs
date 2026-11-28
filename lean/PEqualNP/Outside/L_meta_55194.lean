import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55194 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198461 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [2, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.not, [7]⟩, ⟨.not, [4]⟩, ⟨.not, [5]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [8, 14]⟩, ⟨.or, [6, 15]⟩], 16⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
