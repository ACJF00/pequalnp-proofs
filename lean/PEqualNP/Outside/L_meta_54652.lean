import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54652

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [4, 2]⟩,
      ⟨GateOp.or, [8, 5]⟩,
      ⟨GateOp.or, [11, 10]⟩,
      ⟨GateOp.or, [12, 6]⟩,
      ⟨GateOp.or, [11, 9]⟩,
      ⟨GateOp.and, [14, 0]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.and, [13, 1]⟩,
      ⟨GateOp.or, [5, 16]⟩,
      ⟨GateOp.or, [18, 3]⟩,
      ⟨GateOp.and, [19, 10]⟩,
      ⟨GateOp.or, [15, 20]⟩,
      ⟨GateOp.or, [17, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (321010 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54652

theorem PEqualNP.Outside.L_meta_54652 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321010 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_54652.ckt, PEqualNP.Outside.L_meta_54652.mono, by decide, PEqualNP.Outside.L_meta_54652.rep⟩
