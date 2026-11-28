import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55067

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.and, [5, 1]⟩, ⟨.or, [4, 1]⟩, ⟨.and, [2, 7]⟩,
    ⟨.or, [3, 0]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [3, 10]⟩,
    ⟨.or, [2, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [9, 13]⟩,
    ⟨.or, [8, 14]⟩, ⟨.or, [6, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_55067

theorem PEqualNP.Outside.L_meta_55067 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165563 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_55067.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_55067.witness]
