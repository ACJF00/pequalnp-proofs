import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54632

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 6]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [2, 7]⟩,
      ⟨GateOp.or, [5, 11]⟩,
      ⟨GateOp.or, [10, 13]⟩,
      ⟨GateOp.or, [3, 5]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [13, 16]⟩,
      ⟨GateOp.and, [10, 17]⟩,
      ⟨GateOp.and, [11, 15]⟩,
      ⟨GateOp.and, [12, 14]⟩,
      ⟨GateOp.or, [18, 19]⟩,
      ⟨GateOp.or, [21, 20]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (291771 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54632

theorem PEqualNP.Outside.L_meta_54632 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (291771 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_54632.ckt, PEqualNP.Outside.L_meta_54632.mono, by decide, PEqualNP.Outside.L_meta_54632.rep⟩
