import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54052

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.and, [1, 7]⟩,
      ⟨GateOp.not, [9]⟩,
      ⟨GateOp.and, [6, 10]⟩,
      ⟨GateOp.and, [2, 4]⟩,
      ⟨GateOp.and, [3, 8]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [14, 13]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4294589 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_54052

theorem PEqualNP.Outside.L_meta_54052 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4294589 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_54052.ckt, PEqualNP.Outside.L_meta_54052.fan, by decide, PEqualNP.Outside.L_meta_54052.ev⟩
