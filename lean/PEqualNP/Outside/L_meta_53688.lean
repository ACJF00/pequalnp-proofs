import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53688 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (274814 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [0, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [1, 5]⟩,
    ⟨.or, [7, 8]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [13, 14]⟩,
    ⟨.and, [10, 15]⟩, ⟨.or, [16, 12]⟩, ⟨.and, [10, 17]⟩,
    ⟨.or, [18, 11]⟩, ⟨.or, [10, 17]⟩, ⟨.and, [20, 19]⟩], 21⟩
  refine ⟨C, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
