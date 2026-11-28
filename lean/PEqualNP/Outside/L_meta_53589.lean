import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53589 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (904191 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [2, 11]⟩,
    ⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [13, 14]⟩,
    ⟨.or, [9, 10]⟩, ⟨.and, [1, 16]⟩, ⟨.or, [12, 15]⟩,
    ⟨.or, [17, 18]⟩, ⟨.or, [0, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
