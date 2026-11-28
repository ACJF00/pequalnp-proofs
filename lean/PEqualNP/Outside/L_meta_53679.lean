import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53679

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.or, [2, 6]⟩,
      ⟨GateOp.or, [7, 11]⟩,
      ⟨GateOp.or, [3, 8]⟩,
      ⟨GateOp.or, [9, 13]⟩,
      ⟨GateOp.or, [12, 14]⟩,
      ⟨GateOp.and, [12, 14]⟩,
      ⟨GateOp.and, [10, 15]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [18, 0]⟩,
      ⟨GateOp.or, [19, 4]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (4145023 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53679

theorem PEqualNP.Outside.L_meta_53679 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4145023 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53679.ckt, PEqualNP.Outside.L_meta_53679.mono, by decide, PEqualNP.Outside.L_meta_53679.rep⟩
