import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53734

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [10, 7]⟩, ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.or, [12, 9]⟩, ⟨GateOp.or, [12, 8]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [19, 17]⟩, ⟨GateOp.or, [20, 18]⟩], 21⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (288751 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨wit, wit_mono, by decide, by decide⟩

end PEqualNP.Outside.L_meta_53734

theorem PEqualNP.Outside.L_meta_53734 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (288751 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  PEqualNP.Outside.L_meta_53734.main_aux
