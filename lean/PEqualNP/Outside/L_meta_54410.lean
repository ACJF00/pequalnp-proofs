import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54410

def circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [⟨.or, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [0, 4]⟩,
              ⟨.or, [1, 12]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [3, 14]⟩,
              ⟨.and, [13, 15]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [2, 11]⟩,
              ⟨.or, [1, 18]⟩, ⟨.and, [17, 19]⟩, ⟨.or, [16, 20]⟩]
    output := 21 }

end PEqualNP.Outside.L_meta_54410

theorem PEqualNP.Outside.L_meta_54410 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (291838 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_54410.circuit, ?_, by decide, ?_⟩
  · intro gate membership
    simp only [PEqualNP.Outside.L_meta_54410.circuit, List.mem_cons, List.not_mem_nil,
      or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
