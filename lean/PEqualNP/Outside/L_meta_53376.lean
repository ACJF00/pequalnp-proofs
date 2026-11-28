import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53376
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def witness : Circuit := ⟨[⟨.or, [2, 4]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [3, 2]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [7, 11]⟩], 12⟩
theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem checked : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266716 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨witness, fan, by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_53376

theorem PEqualNP.Outside.L_meta_53376 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266716 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := @PEqualNP.Outside.L_meta_53376.checked
