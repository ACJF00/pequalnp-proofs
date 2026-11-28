import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54672_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first two gates merge columns with identical truth-table entries.
private def witness : Circuit :=
  { gates :=
      [{ op := GateOp.or, inputs := [5, 6] },
       { op := GateOp.or, inputs := [8, 9] },
       { op := GateOp.and, inputs := [2, 10] },
       { op := GateOp.or, inputs := [1, 7] },
       { op := GateOp.or, inputs := [2, 11] },
       { op := GateOp.or, inputs := [12, 13] },
       { op := GateOp.or, inputs := [10, 14] },
       { op := GateOp.or, inputs := [3, 15] },
       { op := GateOp.and, inputs := [15, 16] },
       { op := GateOp.or, inputs := [16, 17] },
       { op := GateOp.or, inputs := [0, 18] },
       { op := GateOp.or, inputs := [4, 20] },
       { op := GateOp.and, inputs := [19, 21] }],
    output := 22 }

-- Finite witness-check pattern adapted from e44b4bfc89bbff1a6bfc442a069acd637e080af4,
-- lean/PEqualNP/Outside/L_meta_22246.lean, using the new gate list.
lemma witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma witness_rep : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 6) => (327166 : ℕ).testBit (6 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_54672_aux

theorem PEqualNP.Outside.L_meta_54672 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (327166 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨_, PEqualNP.Outside.L_meta_54672_aux.witness_mono, by decide,
    PEqualNP.Outside.L_meta_54672_aux.witness_rep⟩
