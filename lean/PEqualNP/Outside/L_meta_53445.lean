import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53445

open PEqualNP.CircuitLowerBounds

-- The first two rows share the union of columns 2 and 3.
-- The last two rows have the same set of neighbors.
def witness : Circuit where
  gates := [
    ⟨.or, [6, 7]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [10, 8]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.and, [1, 13]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [16, 17]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [18, 19]⟩]
  output := 20

theorem witness_mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness]

theorem witness_correct :
    PEqualNP.Represents.Represents
      (fun (u : Fin 4) (v : Fin 6) => (800557 : ℕ).testBit (6 * u.val + v.val)) witness := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_53445

theorem PEqualNP.Outside.L_meta_53445 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (800557 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_53445.witness, PEqualNP.Outside.L_meta_53445.witness_mono,
    by decide, PEqualNP.Outside.L_meta_53445.witness_correct⟩
