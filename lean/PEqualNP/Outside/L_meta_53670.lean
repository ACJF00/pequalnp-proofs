import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.and, [0, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [9, 10]⟩,
    ⟨.or, [12, 14]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [3, 15]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [5, 18]⟩,
    ⟨.or, [4, 19]⟩], 20⟩

theorem witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

theorem witness_size : witness.size ≤ 11 := by
  decide

theorem witness_rep :
    Represents (fun (u : Fin 4) (v : Fin 6) => (3996919 : ℕ).testBit (6 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_53670

theorem PEqualNP.Outside.L_meta_53670 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (3996919 : ℕ).testBit (6 * u.val + v.val)) 11) :=
  ⟨PEqualNP.Outside.L_meta_53670.witness,
   PEqualNP.Outside.L_meta_53670.witness_mono,
   PEqualNP.Outside.L_meta_53670.witness_size,
   PEqualNP.Outside.L_meta_53670.witness_rep⟩
