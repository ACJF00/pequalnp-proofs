import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54689

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 20]⟩], 21⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (808633 : ℕ).testBit (6 * u.val + v.val)) C := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_54689

theorem PEqualNP.Outside.L_meta_54689 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808633 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_54689.C, PEqualNP.Outside.L_meta_54689.mono, by decide, PEqualNP.Outside.L_meta_54689.rep⟩
