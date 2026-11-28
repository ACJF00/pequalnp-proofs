import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53870

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.and, [0, 1]⟩,
      ⟨GateOp.and, [1, 2]⟩,
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.or, [9, 8]⟩,
      ⟨GateOp.not, [10]⟩,
      ⟨GateOp.and, [6, 11]⟩,
      ⟨GateOp.and, [3, 2]⟩,
      ⟨GateOp.or, [12, 13]⟩
    ],
    output := 14 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36021 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_53870

theorem PEqualNP.Outside.L_meta_53870 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36021 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_53870.ckt, PEqualNP.Outside.L_meta_53870.fan, by decide, PEqualNP.Outside.L_meta_53870.ev⟩
