import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_57910_aux

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [5, 12]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.not, [16]⟩, ⟨.or, [11, 17]⟩], 18⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_57910_aux

open PEqualNP.Outside.L_meta_57910_aux in
theorem PEqualNP.Outside.L_meta_57910 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165171 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
