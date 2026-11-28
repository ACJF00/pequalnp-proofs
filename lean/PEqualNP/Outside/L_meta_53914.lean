import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53914_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩], 15⟩

def okOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem okOpSound (g : Gate) (ok : okOp g = true) : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [okOp, h] at ok ⊢

theorem witnessOk : FanInTwo witness := by
  have legal : witness.gates.all (fun g => okOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using okOpSound g passed.1, passed.2⟩

end PEqualNP.Outside.L_meta_53914_aux

theorem PEqualNP.Outside.L_meta_53914 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (51132 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_53914_aux.witness, PEqualNP.Outside.L_meta_53914_aux.witnessOk, by decide, ?_⟩
  decide +kernel
