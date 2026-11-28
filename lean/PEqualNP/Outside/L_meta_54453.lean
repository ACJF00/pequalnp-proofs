import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54453

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [0, 11]⟩,
    ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [15, 18]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.or, [17, 20]⟩], 21⟩

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

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (387054 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨wit, monoTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_54453

theorem PEqualNP.Outside.L_meta_54453 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (387054 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  PEqualNP.Outside.L_meta_54453.main_aux
