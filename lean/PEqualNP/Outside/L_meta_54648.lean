import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54648 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (320943 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [5, 6]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [4, 9]⟩,
     ⟨.or, [11, 12]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [0, 13]⟩,
     ⟨.and, [1, 14]⟩, ⟨.and, [2, 11]⟩, ⟨.and, [3, 4]⟩,
     ⟨.or, [15, 16]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [20, 18]⟩], 21⟩
  refine ⟨C, ?_, by decide, by decide⟩
  simp [C, PEqualNP.MetaComplexity.Monotone2]
