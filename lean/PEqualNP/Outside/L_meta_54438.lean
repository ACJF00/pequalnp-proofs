import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54438_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The last eleven gates adapt lean/PEqualNP/Outside/L_meta_21277.lean at
-- d667e87931366d16a0380297f19024953d7b1db3 by merging the two identical columns.
-- That witness credits the live-set search in L_meta_5469.lean and L_meta_5475.lean.
private def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [0, 4] },
      { op := GateOp.or, inputs := [1, 3] }, { op := GateOp.or, inputs := [13, 9] },
      { op := GateOp.and, inputs := [14, 12] }, { op := GateOp.or, inputs := [10, 7] },
      { op := GateOp.and, inputs := [16, 2] }, { op := GateOp.or, inputs := [17, 15] },
      { op := GateOp.or, inputs := [10, 8] }, { op := GateOp.and, inputs := [19, 11] },
      { op := GateOp.or, inputs := [20, 18] }],
    output := 21 }

private theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem upper_rep : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 6) => (321014 : ℕ).testBit (6 * u.val + v.val)) upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_54438_aux

theorem PEqualNP.Outside.L_meta_54438 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321014 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  exact ⟨PEqualNP.Outside.L_meta_54438_aux.upperC, PEqualNP.Outside.L_meta_54438_aux.upper_mono,
    by decide, PEqualNP.Outside.L_meta_54438_aux.upper_rep⟩
