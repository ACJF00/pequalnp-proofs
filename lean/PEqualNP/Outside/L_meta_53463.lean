import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53463

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [11, 7]⟩,
      ⟨GateOp.and, [10, 13]⟩,
      ⟨GateOp.or, [0, 14]⟩,
      ⟨GateOp.or, [6, 3]⟩,
      ⟨GateOp.and, [12, 16]⟩,
      ⟨GateOp.or, [15, 17]⟩
    ],
    output := 18 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (807871 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53463

theorem PEqualNP.Outside.L_meta_53463 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807871 : ℕ).testBit (6 * u.val + v.val)) 9 :=
  ⟨PEqualNP.Outside.L_meta_53463.ckt, PEqualNP.Outside.L_meta_53463.mono, by decide, PEqualNP.Outside.L_meta_53463.rep⟩
