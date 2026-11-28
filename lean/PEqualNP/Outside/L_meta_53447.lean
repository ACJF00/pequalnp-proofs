import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53447 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (800623 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }], output := 20 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
