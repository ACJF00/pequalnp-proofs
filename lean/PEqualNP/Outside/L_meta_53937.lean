import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53937

open PEqualNP.CircuitLowerBounds

private def witnessCircuit : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [0, 5] }
      , { op := GateOp.and, inputs := [1, 6] }
      , { op := GateOp.or, inputs := [2, 7] }
      , { op := GateOp.or, inputs := [3, 4] }
      , { op := GateOp.not, inputs := [9] }
      , { op := GateOp.and, inputs := [8, 10] }
      , { op := GateOp.not, inputs := [11] }
      , { op := GateOp.or, inputs := [0, 1] }
      , { op := GateOp.or, inputs := [13, 2] }
      , { op := GateOp.and, inputs := [12, 14] }
      ]
    output := 15 }

end PEqualNP.Outside.L_meta_53937

theorem PEqualNP.Outside.L_meta_53937 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100025 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_53937.witnessCircuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_53937.witnessCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
