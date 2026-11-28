import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53904
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.not, [1]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.not, [8]⟩,
  ⟨.and, [2, 10]⟩,
  ⟨.or, [6, 11]⟩,
  ⟨.and, [9, 12]⟩], 13⟩

lemma fanin : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_53904

open PEqualNP.Outside.L_meta_53904 in
theorem PEqualNP.Outside.L_meta_53904 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52285 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, fanin, by decide, by decide +kernel⟩
