import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53651 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947384 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [7, 8]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [4, 5]⟩,
    ⟨.or, [0, 12]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [9, 11]⟩,
    ⟨.or, [13, 11]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [13, 6]⟩,
    ⟨.and, [18, 15]⟩, ⟨.or, [17, 19]⟩], 20⟩
  refine ⟨C, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
