import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53302

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [5, 4]⟩,
      ⟨GateOp.and, [0, 6]⟩,
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.and, [1, 8]⟩,
      ⟨GateOp.and, [2, 3]⟩,
      ⟨GateOp.or, [7, 9]⟩,
      ⟨GateOp.or, [11, 10]⟩
    ],
    output := 12 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8598 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_53302

theorem PEqualNP.Outside.L_meta_53302 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8598 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_53302.ckt, PEqualNP.Outside.L_meta_53302.fan, by decide, PEqualNP.Outside.L_meta_53302.ev⟩
