import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53439

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def witness : Circuit :=
  ⟨[⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [10, 7]⟩,
    ⟨GateOp.or, [11, 4]⟩,
    ⟨GateOp.or, [12, 9]⟩,
    ⟨GateOp.or, [11, 8]⟩,
    ⟨GateOp.and, [1, 13]⟩,
    ⟨GateOp.and, [2, 14]⟩,
    ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [0, 15]⟩,
    ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.or, [18, 19]⟩], 20⟩

private theorem witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem bound : RepSizeAtMost
    (fun (u : Fin 4) (v : Fin 6) => (388095 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨witness, witness_mono, by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_53439

theorem PEqualNP.Outside.L_meta_53439 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (388095 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact PEqualNP.Outside.L_meta_53439.bound
