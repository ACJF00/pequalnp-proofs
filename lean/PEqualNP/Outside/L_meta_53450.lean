import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53450

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [0, 16]⟩], 17⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 8 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (807359 : ℕ).testBit (6 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_53450

theorem PEqualNP.Outside.L_meta_53450 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807359 : ℕ).testBit (6 * u.val + v.val)) 8) :=
  ⟨PEqualNP.Outside.L_meta_53450.witness, PEqualNP.Outside.L_meta_53450.mono, PEqualNP.Outside.L_meta_53450.small, PEqualNP.Outside.L_meta_53450.rep⟩
