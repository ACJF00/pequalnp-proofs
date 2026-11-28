import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53441

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def witness : Circuit where
  gates := [
    -- Wires 10 to 12 combine vertices with identical neighborhoods.
    ⟨.or, [2, 3]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [11, 9]⟩,
    -- Wires 13 to 20 compute the adjacency on those vertex groups.
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.and, [13, 17]⟩,
    ⟨.and, [15, 16]⟩,
    ⟨.or, [18, 19]⟩]
  output := 20

private theorem correct :
    Represents (fun (u : Fin 4) (v : Fin 6) => (799102 : ℕ).testBit (6 * u.val + v.val))
      witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_53441

theorem PEqualNP.Outside.L_meta_53441 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (799102 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨PEqualNP.Outside.L_meta_53441.witness, ?_, by decide +kernel,
    PEqualNP.Outside.L_meta_53441.correct⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_53441.witness]