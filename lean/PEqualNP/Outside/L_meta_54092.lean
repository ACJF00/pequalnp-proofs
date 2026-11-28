import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54092

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 13]⟩], 15⟩

def okOp : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | PEqualNP.CircuitLowerBounds.GateOp.and => true
  | PEqualNP.CircuitLowerBounds.GateOp.or => true
  | PEqualNP.CircuitLowerBounds.GateOp.not => true
  | _ => false

def shapeB (C : PEqualNP.CircuitLowerBounds.Circuit) : Bool :=
  C.gates.all fun g => okOp g.op && decide (g.inputs.length ≤ 2)

theorem shapeB_sound {C : PEqualNP.CircuitLowerBounds.Circuit} (h : shapeB C = true) : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  have hp := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  refine ⟨?_, hp.2⟩
  have h1 := hp.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [okOp]

theorem wit_ok : PEqualNP.MetaComplexity.FanInTwo wit := shapeB_sound (by decide +kernel)

theorem wit_size : wit.size ≤ 10 := by decide +kernel

set_option maxRecDepth 200000 in
theorem wit_rep : ∀ i j : Fin 6, wit.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4311995 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_54092

theorem PEqualNP.Outside.L_meta_54092 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4311995 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_54092.wit, PEqualNP.Outside.L_meta_54092.wit_ok, PEqualNP.Outside.L_meta_54092.wit_size,
    PEqualNP.Outside.L_meta_54092.wit_rep⟩
