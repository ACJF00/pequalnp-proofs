import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53461

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [1, 6]⟩,
      ⟨GateOp.or, [2, 10]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [11, 8]⟩,
      ⟨GateOp.or, [14, 9]⟩,
      ⟨GateOp.or, [15, 3]⟩,
      ⟨GateOp.and, [12, 16]⟩,
      ⟨GateOp.or, [17, 7]⟩,
      ⟨GateOp.and, [13, 18]⟩,
      ⟨GateOp.or, [4, 19]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (807677 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_53461

theorem PEqualNP.Outside.L_meta_53461 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807677 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_53461.ckt, PEqualNP.Outside.L_meta_53461.mono, by decide, PEqualNP.Outside.L_meta_53461.rep⟩
