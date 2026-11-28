import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54145

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩], 19⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (270714 : ℕ).testBit (6 * u.val + v.val)) C := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_54145

theorem PEqualNP.Outside.L_meta_54145 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (270714 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_54145.C, PEqualNP.Outside.L_meta_54145.mono, by decide, PEqualNP.Outside.L_meta_54145.rep⟩
