import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54177

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The finite witness proof follows lean/PEqualNP/Outside/L_meta_23684.lean
-- at e44b4bfc89bbff1a6bfc442a069acd637e080af4, with a new gate list.
def witness : Circuit := ⟨[
  ⟨.or, [0, 4]⟩,
  ⟨.or, [1, 10]⟩,
  ⟨.or, [5, 11]⟩,
  ⟨.or, [2, 7]⟩,
  ⟨.or, [6, 13]⟩,
  ⟨.and, [12, 14]⟩,
  ⟨.or, [3, 9]⟩,
  ⟨.or, [8, 16]⟩,
  ⟨.and, [10, 17]⟩,
  ⟨.or, [15, 18]⟩], 19⟩

lemma mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_54177

open PEqualNP.Outside.L_meta_54177 in
theorem PEqualNP.Outside.L_meta_54177 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275260 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
