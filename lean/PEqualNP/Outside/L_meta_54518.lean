import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54518 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (907245 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [6, 7]⟩,
    ⟨.and, [5, 12]⟩, ⟨.and, [13, 11]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [9, 0]⟩,
    ⟨.or, [4, 14]⟩, ⟨.or, [18, 15]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [20, 17]⟩], 21⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
