import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53612

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [7, 8]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [0, 4]⟩,
    ⟨.or, [10, 9]⟩,
    ⟨.or, [3, 13]⟩,
    ⟨.or, [2, 14]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.or, [1, 16]⟩,
    ⟨.or, [0, 17]⟩,
    ⟨.and, [15, 18]⟩,
    ⟨.or, [12, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_53612

theorem PEqualNP.Outside.L_meta_53612 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1867321 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨PEqualNP.Outside.L_meta_53612.circuit, PEqualNP.Outside.L_meta_53612.monotone, by decide, ?_⟩
  decide +kernel
