import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53869_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 3] },
      { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [2, 6] },
      { op := GateOp.or, inputs := [2, 6] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.not, inputs := [9] },
      { op := GateOp.and, inputs := [1, 11] },
      { op := GateOp.or, inputs := [8, 12] },
      { op := GateOp.or, inputs := [10, 13] }],
    output := 14 }

theorem circ_ok : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_53869_aux

theorem PEqualNP.Outside.L_meta_53869 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36020 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_53869_aux.circ, PEqualNP.Outside.L_meta_53869_aux.circ_ok, by decide, by decide +kernel⟩
