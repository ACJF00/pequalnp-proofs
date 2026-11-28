import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_1525 : (∀ (m x y : Nat),
  (∃ a b c d : Nat, a+b+c+d = m ∧
    min a b + min c d = x ∧ min a c + min b d = y) ↔
  2 * max x y + (min x y) % 2 ≤ m) := by
  intro m x y
  constructor
  · rintro ⟨a, b, c, d, h1, h2, h3⟩
    omega
  · intro h
    refine ⟨m - ((x - min x y / 2) + (y - min x y / 2) + min x y / 2),
      x - min x y / 2, y - min x y / 2, min x y / 2, ?_, ?_, ?_⟩ <;> omega
