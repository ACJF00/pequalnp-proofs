import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55125 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197278 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [11]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [6, 15]⟩], 16⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
