import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53459

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 2]⟩,
      ⟨GateOp.or, [10, 5]⟩,
      ⟨GateOp.or, [11, 7]⟩,
      ⟨GateOp.or, [5, 8]⟩,
      ⟨GateOp.or, [13, 9]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.and, [15, 14]⟩,
      ⟨GateOp.or, [16, 1]⟩,
      ⟨GateOp.or, [17, 6]⟩,
      ⟨GateOp.and, [18, 12]⟩,
      ⟨GateOp.or, [19, 4]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (807671 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53459

theorem PEqualNP.Outside.L_meta_53459 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807671 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53459.ckt, PEqualNP.Outside.L_meta_53459.mono, by decide, PEqualNP.Outside.L_meta_53459.rep⟩
