import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53615

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.or, [2, 6]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.and, [0, 12]⟩,
      ⟨GateOp.and, [10, 14]⟩,
      ⟨GateOp.and, [11, 13]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.or, [18, 17]⟩,
      ⟨GateOp.or, [19, 4]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1880945 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53615

theorem PEqualNP.Outside.L_meta_53615 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1880945 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53615.ckt, PEqualNP.Outside.L_meta_53615.mono, by decide, PEqualNP.Outside.L_meta_53615.rep⟩
