import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54508

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [7, 6]⟩,
      ⟨GateOp.and, [0, 9]⟩,
      ⟨GateOp.or, [11, 3]⟩,
      ⟨GateOp.or, [8, 12]⟩,
      ⟨GateOp.or, [5, 1]⟩,
      ⟨GateOp.or, [4, 0]⟩,
      ⟨GateOp.or, [15, 14]⟩,
      ⟨GateOp.or, [2, 16]⟩,
      ⟨GateOp.or, [13, 10]⟩,
      ⟨GateOp.and, [18, 17]⟩,
      ⟨GateOp.and, [15, 14]⟩,
      ⟨GateOp.or, [19, 20]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (903038 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54508

theorem PEqualNP.Outside.L_meta_54508 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (903038 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54508.ckt, PEqualNP.Outside.L_meta_54508.mono, by decide, PEqualNP.Outside.L_meta_54508.rep⟩
