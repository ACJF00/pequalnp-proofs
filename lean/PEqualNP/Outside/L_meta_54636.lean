import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54636

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 4]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [3, 11]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [6, 14]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [8, 17]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [15, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54636

theorem PEqualNP.Outside.L_meta_54636 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292537 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨PEqualNP.Outside.L_meta_54636.circuit, PEqualNP.Outside.L_meta_54636.monotone, by decide, ?_⟩
  decide +kernel
