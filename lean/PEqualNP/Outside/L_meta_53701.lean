import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53701

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [6, 7]⟩,
    ⟨.or, [10, 8]⟩,
    ⟨.or, [4, 0]⟩,
    ⟨.or, [5, 1]⟩,
    ⟨.or, [13, 12]⟩,
    ⟨.or, [13, 9]⟩,
    ⟨.or, [3, 15]⟩,
    ⟨.and, [12, 16]⟩,
    ⟨.or, [11, 17]⟩,
    ⟨.or, [2, 18]⟩,
    ⟨.and, [14, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_53701

theorem PEqualNP.Outside.L_meta_53701 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (276350 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_53701.circuit, PEqualNP.Outside.L_meta_53701.monotone, by decide, ?_⟩
  decide +kernel
