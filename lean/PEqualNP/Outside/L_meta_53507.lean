import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53507

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [10, 6]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.or, [2, 7]⟩,
      ⟨GateOp.or, [13, 8]⟩,
      ⟨GateOp.or, [14, 12]⟩,
      ⟨GateOp.or, [14, 9]⟩,
      ⟨GateOp.and, [16, 11]⟩,
      ⟨GateOp.or, [17, 4]⟩,
      ⟨GateOp.or, [18, 5]⟩,
      ⟨GateOp.and, [19, 15]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (816699 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53507

theorem PEqualNP.Outside.L_meta_53507 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816699 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53507.ckt, PEqualNP.Outside.L_meta_53507.mono, by decide, PEqualNP.Outside.L_meta_53507.rep⟩
