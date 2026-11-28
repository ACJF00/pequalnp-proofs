import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54698

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 20]⟩], 21⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (808890 : ℕ).testBit (6 * u.val + v.val)) C := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_54698

theorem PEqualNP.Outside.L_meta_54698 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808890 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_54698.C, PEqualNP.Outside.L_meta_54698.mono, by decide, PEqualNP.Outside.L_meta_54698.rep⟩
