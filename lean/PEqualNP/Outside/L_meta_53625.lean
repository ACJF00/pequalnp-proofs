import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53625

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 6]⟩,
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [5, 12]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.or, [11, 14]⟩,
      ⟨GateOp.and, [13, 15]⟩,
      ⟨GateOp.and, [11, 10]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [18, 0]⟩
    ],
    output := 19 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1881919 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53625

theorem PEqualNP.Outside.L_meta_53625 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881919 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_53625.ckt, PEqualNP.Outside.L_meta_53625.mono, by decide, PEqualNP.Outside.L_meta_53625.rep⟩
