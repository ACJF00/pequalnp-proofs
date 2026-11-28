import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54687

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 20]⟩], 21⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (808622 : ℕ).testBit (6 * u.val + v.val)) C := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_54687

theorem PEqualNP.Outside.L_meta_54687 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808622 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_54687.C, PEqualNP.Outside.L_meta_54687.mono, by decide, PEqualNP.Outside.L_meta_54687.rep⟩
