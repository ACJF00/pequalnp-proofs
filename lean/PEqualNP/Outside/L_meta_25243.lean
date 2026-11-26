import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25243_aux
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  ⟨[⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.and, [2, 11]⟩,
    ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem ev : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (50604 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_25243_aux

theorem PEqualNP.Outside.L_meta_25243 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50604 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_25243_aux.C, PEqualNP.Outside.L_meta_25243_aux.fan, by decide,
    PEqualNP.Outside.L_meta_25243_aux.ev⟩
