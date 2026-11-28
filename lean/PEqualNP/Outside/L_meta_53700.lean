import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53700 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (276271 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [6, 7]⟩,
      ⟨.or, [0, 2]⟩,
      ⟨.or, [0, 4]⟩,
      ⟨.or, [1, 4]⟩,
      ⟨.or, [11, 10]⟩,
      ⟨.or, [13, 5]⟩,
      ⟨.or, [10, 9]⟩,
      ⟨.or, [14, 8]⟩,
      ⟨.and, [15, 17]⟩,
      ⟨.or, [16, 3]⟩,
      ⟨.and, [12, 19]⟩,
      ⟨.or, [18, 20]⟩], 21⟩
  exact ⟨C, by simp [C, PEqualNP.MetaComplexity.Monotone2], by decide, by decide⟩
