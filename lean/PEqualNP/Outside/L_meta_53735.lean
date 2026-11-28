import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53735

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 20]⟩], 21⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (290493 : ℕ).testBit (6 * u.val + v.val)) C := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_53735

theorem PEqualNP.Outside.L_meta_53735 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (290493 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_53735.C, PEqualNP.Outside.L_meta_53735.mono, by decide, PEqualNP.Outside.L_meta_53735.rep⟩
