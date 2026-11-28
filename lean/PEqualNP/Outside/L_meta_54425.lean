import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54425

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 8]⟩,
      ⟨GateOp.or, [3, 2]⟩,
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [9, 10]⟩,
      ⟨GateOp.or, [13, 7]⟩,
      ⟨GateOp.or, [6, 1]⟩,
      ⟨GateOp.and, [15, 12]⟩,
      ⟨GateOp.or, [15, 12]⟩,
      ⟨GateOp.and, [14, 17]⟩,
      ⟨GateOp.and, [11, 4]⟩,
      ⟨GateOp.or, [19, 18]⟩,
      ⟨GateOp.or, [20, 16]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (294588 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54425

theorem PEqualNP.Outside.L_meta_54425 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (294588 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54425.ckt, PEqualNP.Outside.L_meta_54425.mono, by decide, PEqualNP.Outside.L_meta_54425.rep⟩
