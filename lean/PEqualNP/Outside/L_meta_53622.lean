import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53622

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 8]⟩,
      ⟨GateOp.or, [2, 6]⟩,
      ⟨GateOp.or, [1, 7]⟩,
      ⟨GateOp.or, [9, 12]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.or, [12, 14]⟩,
      ⟨GateOp.and, [11, 15]⟩,
      ⟨GateOp.and, [10, 13]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [18, 4]⟩,
      ⟨GateOp.or, [19, 5]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1881583 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53622

theorem PEqualNP.Outside.L_meta_53622 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881583 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53622.ckt, PEqualNP.Outside.L_meta_53622.mono, by decide, PEqualNP.Outside.L_meta_53622.rep⟩
