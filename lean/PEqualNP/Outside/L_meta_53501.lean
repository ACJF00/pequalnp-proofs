import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53501

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [5, 11]⟩,
      ⟨GateOp.or, [1, 12]⟩,
      ⟨GateOp.or, [6, 12]⟩,
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.and, [14, 17]⟩,
      ⟨GateOp.and, [10, 13]⟩,
      ⟨GateOp.or, [18, 19]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (816120 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53501

theorem PEqualNP.Outside.L_meta_53501 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816120 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53501.ckt, PEqualNP.Outside.L_meta_53501.mono, by decide, PEqualNP.Outside.L_meta_53501.rep⟩
