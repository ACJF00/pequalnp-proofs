import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56087
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [1, 2]⟩,
  ⟨.and, [1, 2]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.and, [5, 6]⟩,
  ⟨.not, [8]⟩,
  ⟨.or, [0, 10]⟩,
  ⟨.or, [7, 9]⟩,
  ⟨.or, [11, 12]⟩], 13⟩

lemma fanin : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_56087

open PEqualNP.Outside.L_meta_56087 in
theorem PEqualNP.Outside.L_meta_56087 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274860351 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, fanin, by decide, by decide +kernel⟩
