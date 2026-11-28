import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55035

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [1, 6]⟩,
    ⟨GateOp.or, [5, 7]⟩,
    ⟨GateOp.not, [8]⟩,
    ⟨GateOp.and, [3, 9]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.and, [1, 6]⟩,
    ⟨GateOp.and, [2, 4]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.or, [14, 15]⟩
  ], 16⟩

lemma witness_fanin : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma witness_size : witness.size ≤ 11 := by
  decide

lemma witness_eval : ∀ i j : Fin 6,
    witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2163998 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_55035

theorem PEqualNP.Outside.L_meta_55035 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2163998 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_55035.witness,
   PEqualNP.Outside.L_meta_55035.witness_fanin,
   PEqualNP.Outside.L_meta_55035.witness_size,
   PEqualNP.Outside.L_meta_55035.witness_eval⟩
