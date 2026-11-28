import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54449

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.and, [10, 3]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [7, 11]⟩,
      ⟨GateOp.or, [5, 10]⟩,
      ⟨GateOp.or, [1, 13]⟩,
      ⟨GateOp.or, [12, 2]⟩,
      ⟨GateOp.or, [6, 15]⟩,
      ⟨GateOp.and, [14, 17]⟩,
      ⟨GateOp.or, [14, 17]⟩,
      ⟨GateOp.or, [18, 16]⟩,
      ⟨GateOp.and, [20, 19]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (326908 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54449

theorem PEqualNP.Outside.L_meta_54449 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (326908 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54449.ckt, PEqualNP.Outside.L_meta_54449.mono, by decide, PEqualNP.Outside.L_meta_54449.rep⟩
