import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54000

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.not, [7]⟩,
      ⟨GateOp.and, [6, 9]⟩,
      ⟨GateOp.and, [0, 1]⟩,
      ⟨GateOp.and, [8, 3]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [13, 12]⟩,
      ⟨GateOp.not, [14]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2117053 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_54000

theorem PEqualNP.Outside.L_meta_54000 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2117053 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_54000.ckt, PEqualNP.Outside.L_meta_54000.fan, by decide, PEqualNP.Outside.L_meta_54000.ev⟩
