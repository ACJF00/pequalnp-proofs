import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53268

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [3]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [8, 10]⟩], 11⟩

def fanInTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem fanInTwoB_sound (C : Circuit) (h : fanInTwoB C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main_aux : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283615 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨wit, fanInTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_53268

theorem PEqualNP.Outside.L_meta_53268 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283615 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_53268.main_aux
