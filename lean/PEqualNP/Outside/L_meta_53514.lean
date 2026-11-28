import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53514

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [10, 5]⟩,
      ⟨GateOp.or, [11, 1]⟩,
      ⟨GateOp.or, [12, 6]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [14, 9]⟩,
      ⟨GateOp.and, [15, 11]⟩,
      ⟨GateOp.or, [16, 2]⟩,
      ⟨GateOp.or, [17, 7]⟩,
      ⟨GateOp.or, [18, 8]⟩,
      ⟨GateOp.and, [19, 13]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (816888 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53514

theorem PEqualNP.Outside.L_meta_53514 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816888 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53514.ckt, PEqualNP.Outside.L_meta_53514.mono, by decide, PEqualNP.Outside.L_meta_53514.rep⟩
