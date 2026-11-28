import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54461_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.or, [3, 12]⟩,
    ⟨.or, [6, 13]⟩,
    ⟨.or, [7, 14]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.and, [15, 16]⟩,
    ⟨.or, [9, 18]⟩,
    ⟨.and, [16, 19]⟩,
    ⟨.or, [17, 20]⟩], 21⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_54461_aux

open PEqualNP.Outside.L_meta_54461_aux in
theorem PEqualNP.Outside.L_meta_54461 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (802686 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨witness, mono, by decide, by decide⟩
