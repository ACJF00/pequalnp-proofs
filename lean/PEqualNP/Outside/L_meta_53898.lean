import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53898
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def witness : Circuit := ⟨[⟨.or, [5, 4]⟩, ⟨.and, [6, 0]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [5, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩
theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem checked : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (51122 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, fan, by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_53898

theorem PEqualNP.Outside.L_meta_53898 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (51122 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := @PEqualNP.Outside.L_meta_53898.checked
