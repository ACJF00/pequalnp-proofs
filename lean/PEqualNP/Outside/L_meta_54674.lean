import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54674 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (800638 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨(⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.or, [10, 8]⟩,
    ⟨.or, [11, 5]⟩,
    ⟨.or, [12, 9]⟩,
    ⟨.or, [11, 4]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [0, 13]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.and, [16, 15]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [20, 19]⟩
  ], 21⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, Set.mem_insert_iff]
  · intro u v
    fin_cases u <;> fin_cases v <;> decide
