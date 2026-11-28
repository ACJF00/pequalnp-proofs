import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54484

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [1, 12]⟩,
    ⟨GateOp.and, [3, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.and, [15, 16]⟩,
    ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [2, 18]⟩, ⟨GateOp.or, [17, 19]⟩, ⟨GateOp.or, [14, 20]⟩], 21⟩

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

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808506 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨wit, monoTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_54484

theorem PEqualNP.Outside.L_meta_54484 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808506 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  PEqualNP.Outside.L_meta_54484.main_aux
