import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53598.Aux

open PEqualNP.CircuitLowerBounds

/-- Wires 0 through 3 select a row, and wires 4 through 9 select a column.
    Each subsequent wire is the output of the next gate in this list. -/
def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
     ⟨.or, [4, 5]⟩,
     ⟨.or, [6, 7]⟩,
     ⟨.or, [12, 8]⟩,
     ⟨.or, [13, 9]⟩,
     ⟨.or, [13, 4]⟩,
     ⟨.and, [10, 14]⟩,
     ⟨.and, [2, 15]⟩,
     ⟨.and, [3, 11]⟩,
     ⟨.or, [16, 17]⟩,
     ⟨.or, [19, 18]⟩], 20⟩

end PEqualNP.Outside.L_meta_53598.Aux

theorem PEqualNP.Outside.L_meta_53598 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (909116 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨PEqualNP.Outside.L_meta_53598.Aux.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.Outside.L_meta_53598.Aux.witness, PEqualNP.MetaComplexity.Monotone2]
