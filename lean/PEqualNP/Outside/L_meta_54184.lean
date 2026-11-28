import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_54184 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (276268 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  let witness : Circuit :=
    ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [12, 7]⟩,
      ⟨.or, [13, 3]⟩, ⟨.or, [14, 9]⟩, ⟨.and, [15, 10]⟩, ⟨.or, [13, 8]⟩,
      ⟨.and, [17, 11]⟩, ⟨.or, [18, 16]⟩], 19⟩
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro gate member
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · dsimp only [witness]
    decide
  · dsimp only [witness]
    decide +kernel
