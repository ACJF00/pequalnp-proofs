import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54176

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 18]⟩], 19⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (275252 : ℕ).testBit (6 * u.val + v.val)) C := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_54176

theorem PEqualNP.Outside.L_meta_54176 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275252 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_54176.C, PEqualNP.Outside.L_meta_54176.mono, by decide, PEqualNP.Outside.L_meta_54176.rep⟩
