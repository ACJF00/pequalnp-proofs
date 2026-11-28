import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54392

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def witness : Circuit :=
  ⟨[⟨.or, [6, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [4, 17]⟩, ⟨.and, [18, 19]⟩], 20⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (324606 : ℕ).testBit (6 * u.val + v.val)) witness := by
  decide +kernel

theorem solve : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (324606 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨witness, by simp [Monotone2, witness], by decide, witness_ok⟩

end PEqualNP.Outside.L_meta_54392

theorem PEqualNP.Outside.L_meta_54392 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (324606 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_54392.solve
