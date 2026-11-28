import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53567

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [4, 10]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.and, [15, 12]⟩,
      ⟨GateOp.and, [2, 13]⟩,
      ⟨GateOp.and, [3, 14]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [19, 18]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (843580 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53567

theorem PEqualNP.Outside.L_meta_53567 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843580 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53567.ckt, PEqualNP.Outside.L_meta_53567.mono, by decide, PEqualNP.Outside.L_meta_53567.rep⟩
