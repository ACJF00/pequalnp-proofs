import PEqualNP.Defs

-- File shape copied from the merged L-meta-22544 (green-notes, 26 Nov). The circuit is found by our
-- notes/tools/improve/gen/rect46.py with the live-set search of the merged L_meta_6343 (Bastian Milan, PR 12547).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_54676 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (807550 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  let C : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [15, 14]⟩, ⟨.and, [16, 12]⟩, ⟨.or, [17, 11]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [20, 19]⟩, ⟨.or, [21, 18]⟩], 22⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
