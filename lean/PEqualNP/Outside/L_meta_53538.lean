import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53538

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [0, 2]⟩,
      ⟨GateOp.or, [11, 4]⟩,
      ⟨GateOp.or, [12, 5]⟩,
      ⟨GateOp.or, [4, 8]⟩,
      ⟨GateOp.or, [14, 9]⟩,
      ⟨GateOp.and, [15, 10]⟩,
      ⟨GateOp.or, [3, 6]⟩,
      ⟨GateOp.or, [17, 7]⟩,
      ⟨GateOp.and, [18, 13]⟩,
      ⟨GateOp.or, [19, 16]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (838781 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53538

theorem PEqualNP.Outside.L_meta_53538 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838781 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53538.ckt, PEqualNP.Outside.L_meta_53538.mono, by decide, PEqualNP.Outside.L_meta_53538.rep⟩
