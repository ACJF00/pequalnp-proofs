import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53333
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def witness : Circuit := ⟨[⟨.or, [4, 3]⟩, ⟨.and, [5, 0]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [6, 10]⟩], 11⟩
theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem checked : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4318 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨witness, fan, by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_53333

theorem PEqualNP.Outside.L_meta_53333 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4318 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := @PEqualNP.Outside.L_meta_53333.checked
