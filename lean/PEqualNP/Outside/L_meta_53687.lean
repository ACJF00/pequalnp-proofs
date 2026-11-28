import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53687_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.and, [0, 14]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [19, 20]⟩], 21⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_53687_aux

open PEqualNP.Outside.L_meta_53687_aux in
theorem PEqualNP.Outside.L_meta_53687 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (272239 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨witness, mono, by decide, by decide⟩
