import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53686

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [6, 7]⟩,
    ⟨.or, [10, 5]⟩,
    ⟨.or, [11, 9]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [10, 4]⟩,
    ⟨.or, [14, 8]⟩,
    ⟨.and, [1, 15]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [19, 17]⟩,
    ⟨.or, [20, 18]⟩], 21⟩

lemma monotone : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma represents : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 6) => (272238 : ℕ).testBit (6 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_53686

theorem PEqualNP.Outside.L_meta_53686 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (272238 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_53686.witness, PEqualNP.Outside.L_meta_53686.monotone, by decide,
    PEqualNP.Outside.L_meta_53686.represents⟩
