import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53683

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [4, 6]⟩,
    ⟨.or, [10, 5]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [10, 7]⟩,
    ⟨.and, [0, 13]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [19, 20]⟩], 21⟩

lemma monotone : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma represents : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 6) => (271223 : ℕ).testBit (6 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_53683

theorem PEqualNP.Outside.L_meta_53683 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (271223 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_53683.witness, PEqualNP.Outside.L_meta_53683.monotone, by decide,
    PEqualNP.Outside.L_meta_53683.represents⟩
