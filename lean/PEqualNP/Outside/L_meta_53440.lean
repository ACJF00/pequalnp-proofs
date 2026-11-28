import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53440

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit :=
  { gates :=
      [ ⟨.or, [1, 2]⟩
      , ⟨.or, [0, 10]⟩
      , ⟨.or, [3, 10]⟩
      , ⟨.or, [5, 6]⟩
      , ⟨.or, [7, 8]⟩
      , ⟨.or, [13, 14]⟩
      , ⟨.and, [11, 15]⟩
      , ⟨.and, [12, 4]⟩
      , ⟨.and, [0, 9]⟩
      , ⟨.or, [16, 17]⟩
      , ⟨.or, [19, 18]⟩ ]
    output := 20 }

theorem circuit_mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem circuit_represents :
    Represents (fun (u : Fin 4) (v : Fin 6) => (391166 : ℕ).testBit (6 * u.val + v.val))
      circuit := by
  decide +kernel

end PEqualNP.Outside.L_meta_53440

theorem PEqualNP.Outside.L_meta_53440 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (391166 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_53440.circuit, PEqualNP.Outside.L_meta_53440.circuit_mono,
    by decide, PEqualNP.Outside.L_meta_53440.circuit_represents⟩
