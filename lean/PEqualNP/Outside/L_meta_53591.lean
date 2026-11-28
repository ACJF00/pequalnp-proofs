import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53591_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[
    ⟨.or, [6, 8]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [15, 14]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [19, 18]⟩], 20⟩

theorem monotoneWitness : PEqualNP.MetaComplexity.Monotone2 witness := by
  simp [PEqualNP.MetaComplexity.Monotone2, witness]

end PEqualNP.Outside.L_meta_53591_aux

theorem PEqualNP.Outside.L_meta_53591 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (905085 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_53591_aux.witness, PEqualNP.Outside.L_meta_53591_aux.monotoneWitness,
    by decide, by decide +kernel⟩
