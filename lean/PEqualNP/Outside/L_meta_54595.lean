import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54595 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948667 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨⟨[⟨.or, [5, 4]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [3, 1]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [15, 18]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [20, 10]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
