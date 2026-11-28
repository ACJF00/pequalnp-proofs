import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53411
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def witness : Circuit := ⟨[⟨.and, [0, 3]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [3, 1]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [5, 12]⟩], 13⟩
theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem checked : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4428 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨witness, fan, by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_53411

theorem PEqualNP.Outside.L_meta_53411 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4428 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := @PEqualNP.Outside.L_meta_53411.checked
