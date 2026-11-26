import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_23852_aux

def witness : Circuit :=
  ⟨[⟨.or, [0, 6]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [16, 18]⟩], 19⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_23852_aux

open PEqualNP.Outside.L_meta_23852_aux in
theorem PEqualNP.Outside.L_meta_23852 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881579 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, witnessFit, by decide, by unfold PEqualNP.Represents.Represents; decide +kernel⟩
