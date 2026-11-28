import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54633

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [7, 9]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [4, 7]⟩,
      ⟨GateOp.or, [8, 13]⟩,
      ⟨GateOp.or, [4, 10]⟩,
      ⟨GateOp.and, [0, 12]⟩,
      ⟨GateOp.and, [1, 14]⟩,
      ⟨GateOp.and, [2, 15]⟩,
      ⟨GateOp.and, [3, 4]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [20, 18]⟩,
      ⟨GateOp.or, [21, 19]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (292462 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54633

theorem PEqualNP.Outside.L_meta_54633 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292462 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_54633.ckt, PEqualNP.Outside.L_meta_54633.mono, by decide, PEqualNP.Outside.L_meta_54633.rep⟩
