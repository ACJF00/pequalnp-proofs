import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53676

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 7]⟩,
      ⟨GateOp.or, [1, 8]⟩,
      ⟨GateOp.or, [2, 9]⟩,
      ⟨GateOp.or, [3, 12]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.and, [10, 13]⟩,
      ⟨GateOp.and, [11, 14]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.or, [17, 4]⟩,
      ⟨GateOp.or, [18, 5]⟩,
      ⟨GateOp.or, [19, 6]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (4062199 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53676

theorem PEqualNP.Outside.L_meta_53676 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4062199 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53676.ckt, PEqualNP.Outside.L_meta_53676.mono, by decide, PEqualNP.Outside.L_meta_53676.rep⟩
