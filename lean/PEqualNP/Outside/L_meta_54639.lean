import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54639

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [6, 9]⟩,
    ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.or, [10, 15]⟩, ⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.and, [12, 16]⟩, ⟨GateOp.and, [17, 18]⟩, ⟨GateOp.or, [3, 16]⟩, ⟨GateOp.or, [11, 19]⟩,
    ⟨GateOp.and, [20, 21]⟩], 22⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292541 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨wit, monoTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_54639

theorem PEqualNP.Outside.L_meta_54639 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292541 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  PEqualNP.Outside.L_meta_54639.main_aux
