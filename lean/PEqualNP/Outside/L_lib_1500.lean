import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1500_aux

def HEdges : Finset (Fin 9 × Fin 9) :=
  {(0, 3), (0, 6), (1, 4), (1, 7), (2, 5), (2, 8),
   (3, 7), (3, 8), (4, 8), (6, 7), (6, 8), (7, 8)}

def SH : Finset (Fin 9) := {1, 2, 3, 6}

def coverH (C : Finset (Fin 9)) : Prop :=
  ∀ e ∈ HEdges, e.1 ∈ C ∨ e.2 ∈ C

instance (C : Finset (Fin 9)) : Decidable (coverH C) :=
  Finset.decidableDforallFinset

def sigH (C : Finset (Fin 9)) : Finset (Fin 3) :=
  Finset.univ.filter (fun j : Fin 3 => (⟨j.val, by omega⟩ : Fin 9) ∈ C)

def vcH (X : Finset (Fin 3)) : Finset (Fin 9) :=
  if X = {0} then {0, 4, 5, 7, 8}
  else if X = {1} then {1, 3, 5, 6, 8}
  else if X = {0, 1} then {0, 1, 5, 7, 8}
  else if X = {2} then {2, 3, 4, 6, 7}
  else if X = {0, 2} then {0, 2, 4, 7, 8}
  else if X = {1, 2} then {1, 2, 3, 6, 8}
  else {0, 1, 2, 7, 8}

lemma H_lt : ∀ e ∈ HEdges, e.1 < e.2 := by decide

lemma H_deg : ∀ u : Fin 9, (HEdges.filter (fun e => u = e.1 ∨ u = e.2)).card ≤ 5 := by decide

lemma H_bip : ∀ e ∈ HEdges, e.1 ≠ 8 → e.2 ≠ 8 → (e.1 ∈ SH ↔ e.2 ∉ SH) := by decide

def coverBits (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Bool :=
  (b0 || b3) && (b0 || b6) && (b1 || b4) && (b1 || b7) && (b2 || b5) && (b2 || b8) &&
  (b3 || b7) && (b3 || b8) && (b4 || b8) && (b6 || b7) && (b6 || b8) && (b7 || b8)

def cardBits (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Nat :=
  b0.toNat + b1.toNat + b2.toNat + b3.toNat + b4.toNat + b5.toNat + b6.toNat + b7.toNat + b8.toNat

def vcBits (b0 b1 b2 : Bool) : Fin 9 → Bool :=
  fun r => match r.val with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => !b0 && (b1 || b2)
  | 4 => !b1 && (b0 || b2)
  | 5 => !b2 && (b0 || b1)
  | 6 => !b0 && (b1 || b2)
  | 7 => b0 || (!b1 && b2)
  | _ => b0 || b1

lemma H_min_vc_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    coverBits b0 b1 b2 b3 b4 b5 b6 b7 b8 = true →
    5 ≤ cardBits b0 b1 b2 b3 b4 b5 b6 b7 b8 := by decide

def checkEqBits (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Bool :=
  !(coverBits b0 b1 b2 b3 b4 b5 b6 b7 b8 && decide (cardBits b0 b1 b2 b3 b4 b5 b6 b7 b8 = 5)) ||
  ((b0 || b1 || b2) &&
   (b3 == vcBits b0 b1 b2 3) && (b4 == vcBits b0 b1 b2 4) && (b5 == vcBits b0 b1 b2 5) &&
   (b6 == vcBits b0 b1 b2 6) && (b7 == vcBits b0 b1 b2 7) && (b8 == vcBits b0 b1 b2 8))

lemma H_checkEq_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    checkEqBits b0 b1 b2 b3 b4 b5 b6 b7 b8 = true := by decide

lemma H_eq_vc_bits : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    coverBits b0 b1 b2 b3 b4 b5 b6 b7 b8 = true →
    cardBits b0 b1 b2 b3 b4 b5 b6 b7 b8 = 5 →
    (b0 || b1 || b2) = true ∧
    b3 = vcBits b0 b1 b2 3 ∧ b4 = vcBits b0 b1 b2 4 ∧ b5 = vcBits b0 b1 b2 5 ∧
    b6 = vcBits b0 b1 b2 6 ∧ b7 = vcBits b0 b1 b2 7 ∧ b8 = vcBits b0 b1 b2 8 := by
  intro b0 b1 b2 b3 b4 b5 b6 b7 b8 hcov h5
  have h := H_checkEq_bits b0 b1 b2 b3 b4 b5 b6 b7 b8
  simp only [checkEqBits, hcov, h5, decide_true, Bool.and_true, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma coverH_to_bits (C : Finset (Fin 9)) (hC : coverH C) :
    coverBits (decide ((0 : Fin 9) ∈ C)) (decide ((1 : Fin 9) ∈ C)) (decide ((2 : Fin 9) ∈ C))
      (decide ((3 : Fin 9) ∈ C)) (decide ((4 : Fin 9) ∈ C)) (decide ((5 : Fin 9) ∈ C))
      (decide ((6 : Fin 9) ∈ C)) (decide ((7 : Fin 9) ∈ C)) (decide ((8 : Fin 9) ∈ C)) = true := by
  have he : ∀ u v : Fin 9, (u, v) ∈ HEdges → (decide (u ∈ C) || decide (v ∈ C)) = true := by
    intro u v huv
    rcases hC (u, v) huv with h1 | h2
    · simp [h1]
    · simp [h2]
  simp only [coverBits, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨he 0 3 (by decide), he 0 6 (by decide)⟩, he 1 4 (by decide)⟩,
    he 1 7 (by decide)⟩, he 2 5 (by decide)⟩, he 2 8 (by decide)⟩,
    he 3 7 (by decide)⟩, he 3 8 (by decide)⟩, he 4 8 (by decide)⟩,
    he 6 7 (by decide)⟩, he 6 8 (by decide)⟩, he 7 8 (by decide)⟩

lemma card_eq_cardBits (C : Finset (Fin 9)) :
    C.card = cardBits (decide ((0 : Fin 9) ∈ C)) (decide ((1 : Fin 9) ∈ C)) (decide ((2 : Fin 9) ∈ C))
      (decide ((3 : Fin 9) ∈ C)) (decide ((4 : Fin 9) ∈ C)) (decide ((5 : Fin 9) ∈ C))
      (decide ((6 : Fin 9) ∈ C)) (decide ((7 : Fin 9) ∈ C)) (decide ((8 : Fin 9) ∈ C)) := by
  have h1 : C.card = ∑ r : Fin 9, (decide (r ∈ C)).toNat := by
    rw [Finset.card_eq_sum_ones]
    have : (∑ _r ∈ C, 1) = ∑ r : Fin 9, if r ∈ C then 1 else 0 := by
      rw [← Finset.sum_filter]
      congr 1; ext r; simp
    rw [this]
    apply Finset.sum_congr rfl; intro r _
    by_cases hr : r ∈ C <;> simp [hr]
  rw [h1, Fin.sum_univ_succ, Fin.sum_univ_eight]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, cardBits]
  change (decide ((0 : Fin 9) ∈ C)).toNat + ((decide ((1 : Fin 9) ∈ C)).toNat + (decide ((2 : Fin 9) ∈ C)).toNat +
    (decide ((3 : Fin 9) ∈ C)).toNat + (decide ((4 : Fin 9) ∈ C)).toNat + (decide ((5 : Fin 9) ∈ C)).toNat +
    (decide ((6 : Fin 9) ∈ C)).toNat + (decide ((7 : Fin 9) ∈ C)).toNat + (decide ((8 : Fin 9) ∈ C)).toNat) = _
  omega

lemma vcH_eq_vcBits (X : Finset (Fin 3)) (hX : X.Nonempty) (r : Fin 9) :
    decide (r ∈ vcH X) = vcBits (decide ((0 : Fin 3) ∈ X)) (decide ((1 : Fin 3) ∈ X)) (decide ((2 : Fin 3) ∈ X)) r := by
  revert X hX r
  decide

lemma H_min_vc : ∀ C : Finset (Fin 9), coverH C → 5 ≤ C.card := by
  intro C hC
  rw [card_eq_cardBits C]
  exact H_min_vc_bits _ _ _ _ _ _ _ _ _ (coverH_to_bits C hC)

lemma H_vcH_spec : ∀ X : Finset (Fin 3), X.Nonempty →
    coverH (vcH X) ∧ (vcH X).card = 5 ∧ sigH (vcH X) = X := by decide

lemma H_eq_vcH : ∀ C : Finset (Fin 9), coverH C → C.card = 5 →
    (sigH C).Nonempty ∧ C = vcH (sigH C) := by
  intro C hC h5
  have h5' : cardBits (decide ((0 : Fin 9) ∈ C)) (decide ((1 : Fin 9) ∈ C)) (decide ((2 : Fin 9) ∈ C))
      (decide ((3 : Fin 9) ∈ C)) (decide ((4 : Fin 9) ∈ C)) (decide ((5 : Fin 9) ∈ C))
      (decide ((6 : Fin 9) ∈ C)) (decide ((7 : Fin 9) ∈ C)) (decide ((8 : Fin 9) ∈ C)) = 5 := by
    rw [← card_eq_cardBits C]; exact h5
  obtain ⟨hne, hb3, hb4, hb5, hb6, hb7, hb8⟩ := H_eq_vc_bits _ _ _ _ _ _ _ _ _ (coverH_to_bits C hC) h5'
  have hsig_ne : (sigH C).Nonempty := by
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hne
    rcases hne with (h0 | h1) | h2
    · exact ⟨0, by simp [sigH, h0]⟩
    · exact ⟨1, by simp [sigH, h1]⟩
    · exact ⟨2, by simp [sigH, h2]⟩
  refine ⟨hsig_ne, ?_⟩
  ext r
  have hdec : decide (r ∈ C) = decide (r ∈ vcH (sigH C)) := by
    rw [vcH_eq_vcBits (sigH C) hsig_ne r]
    have h0 : decide ((0 : Fin 3) ∈ sigH C) = decide ((0 : Fin 9) ∈ C) := by simp [sigH]
    have h1 : decide ((1 : Fin 3) ∈ sigH C) = decide ((1 : Fin 9) ∈ C) := by simp [sigH]
    have h2 : decide ((2 : Fin 3) ∈ sigH C) = decide ((2 : Fin 9) ∈ C) := by simp [sigH]
    rw [h0, h1, h2]
    fin_cases r
    · rfl
    · rfl
    · rfl
    · exact hb3
    · exact hb4
    · exact hb5
    · exact hb6
    · exact hb7
    · exact hb8
  exact decide_eq_decide.mp hdec

def equiv9 (m : Nat) : Fin m × Fin 9 ≃ Fin (9 * m) where
  toFun p := ⟨9 * p.1.val + p.2.val, by omega⟩
  invFun u := (⟨u.val / 9, Nat.div_lt_of_lt_mul (by omega)⟩, ⟨u.val % 9, Nat.mod_lt u.val (by omega)⟩)
  left_inv p := by
    ext
    · simp only [Nat.mul_add_div (by omega : 0 < 9), Nat.div_eq_of_lt p.2.isLt, Nat.add_zero]
    · simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt p.2.isLt]
  right_inv u := by
    ext
    exact Nat.div_add_mod u.val 9

def slice9 {m : Nat} (C : Finset (Fin (9 * m))) (i : Fin m) : Finset (Fin 9) :=
  Finset.univ.filter (fun r : Fin 9 => equiv9 m (i, r) ∈ C)

lemma card_eq_sum_slice9 {m : Nat} (C : Finset (Fin (9 * m))) :
    C.card = ∑ i : Fin m, (slice9 C i).card := by
  have h1 : C.card = ∑ u : Fin (9 * m), if u ∈ C then 1 else 0 := by
    simp [Finset.card_filter]
  rw [h1, ← Equiv.sum_comp (equiv9 m), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [slice9, Finset.card_filter]

lemma bipartite_MJ {N : Nat}
    (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (D S C1 C2 : Finset (Fin N))
    (hbip : ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S))
    (h1 : (∀ e ∈ G, e.1 ∈ C1 ∨ e.2 ∈ C1) ∧ ∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C1.sum w ≤ B.sum w)
    (h2 : (∀ e ∈ G, e.1 ∈ C2 ∨ e.2 ∈ C2) ∧ ∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C2.sum w ≤ B.sum w)
    (hD : C1 ∩ D = C2 ∩ D) :
    ∃ M J : Finset (Fin N),
      (∀ x, x ∈ M ↔ (x ∈ D ∧ x ∈ C1) ∨ (x ∉ D ∧ x ∈ S ∧ x ∈ C1 ∧ x ∈ C2) ∨ (x ∉ D ∧ x ∉ S ∧ (x ∈ C1 ∨ x ∈ C2))) ∧
      (∀ x, x ∈ J ↔ (x ∈ D ∧ x ∈ C1) ∨ (x ∉ D ∧ x ∈ S ∧ (x ∈ C1 ∨ x ∈ C2)) ∨ (x ∉ D ∧ x ∉ S ∧ x ∈ C1 ∧ x ∈ C2)) ∧
      ((∀ e ∈ G, e.1 ∈ M ∨ e.2 ∈ M) ∧ ∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → M.sum w ≤ B.sum w) ∧
      ((∀ e ∈ G, e.1 ∈ J ∨ e.2 ∈ J) ∧ ∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → J.sum w ≤ B.sum w) ∧
      (C1 ∩ C2 ⊆ M ∧ M ⊆ C1 ∪ C2) ∧ (C1 ∩ C2 ⊆ J ∧ J ⊆ C1 ∪ C2) := by
  classical
  let M : Finset (Fin N) := Finset.univ.filter fun x =>
    (x ∈ D ∧ x ∈ C1) ∨ (x ∉ D ∧ x ∈ S ∧ x ∈ C1 ∧ x ∈ C2) ∨ (x ∉ D ∧ x ∉ S ∧ (x ∈ C1 ∨ x ∈ C2))
  let J : Finset (Fin N) := Finset.univ.filter fun x =>
    (x ∈ D ∧ x ∈ C1) ∨ (x ∉ D ∧ x ∈ S ∧ (x ∈ C1 ∨ x ∈ C2)) ∨ (x ∉ D ∧ x ∉ S ∧ x ∈ C1 ∧ x ∈ C2)
  have hM_mem : ∀ x, x ∈ M ↔ (x ∈ D ∧ x ∈ C1) ∨ (x ∉ D ∧ x ∈ S ∧ x ∈ C1 ∧ x ∈ C2) ∨ (x ∉ D ∧ x ∉ S ∧ (x ∈ C1 ∨ x ∈ C2)) :=
    fun x => by simp [M]
  have hJ_mem : ∀ x, x ∈ J ↔ (x ∈ D ∧ x ∈ C1) ∨ (x ∉ D ∧ x ∈ S ∧ (x ∈ C1 ∨ x ∈ C2)) ∨ (x ∉ D ∧ x ∉ S ∧ x ∈ C1 ∧ x ∈ C2) :=
    fun x => by simp [J]
  have hD_iff : ∀ x ∈ D, x ∈ C1 ↔ x ∈ C2 := by
    intro x hxD
    have h := Finset.ext_iff.mp hD x
    simp [hxD] at h
    exact h
  have hM_cov : ∀ e ∈ G, e.1 ∈ M ∨ e.2 ∈ M := by
    intro e he
    have hc1 := h1.1 e he
    have hc2 := h2.1 e he
    rw [hM_mem e.1, hM_mem e.2]
    by_cases h1D : e.1 ∈ D
    · by_cases h11 : e.1 ∈ C1
      · exact Or.inl (Or.inl ⟨h1D, h11⟩)
      · have h12 : e.1 ∉ C2 := fun h => h11 ((hD_iff e.1 h1D).mpr h)
        have h21 : e.2 ∈ C1 := hc1.resolve_left h11
        have h22 : e.2 ∈ C2 := hc2.resolve_left h12
        by_cases h2D : e.2 ∈ D
        · exact Or.inr (Or.inl ⟨h2D, h21⟩)
        · by_cases h2S : e.2 ∈ S
          · exact Or.inr (Or.inr (Or.inl ⟨h2D, h2S, h21, h22⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨h2D, h2S, Or.inl h21⟩))
    · by_cases h2D : e.2 ∈ D
      · by_cases h21 : e.2 ∈ C1
        · exact Or.inr (Or.inl ⟨h2D, h21⟩)
        · have h22 : e.2 ∉ C2 := fun h => h21 ((hD_iff e.2 h2D).mpr h)
          have h11 : e.1 ∈ C1 := hc1.resolve_right h21
          have h12 : e.1 ∈ C2 := hc2.resolve_right h22
          by_cases h1S : e.1 ∈ S
          · exact Or.inl (Or.inr (Or.inl ⟨h1D, h1S, h11, h12⟩))
          · exact Or.inl (Or.inr (Or.inr ⟨h1D, h1S, Or.inl h11⟩))
      · have hbi := hbip e he h1D h2D
        by_cases h1S : e.1 ∈ S
        · have h2S : e.2 ∉ S := hbi.mp h1S
          by_cases h11 : e.1 ∈ C1
          · by_cases h12 : e.1 ∈ C2
            · exact Or.inl (Or.inr (Or.inl ⟨h1D, h1S, h11, h12⟩))
            · exact Or.inr (Or.inr (Or.inr ⟨h2D, h2S, Or.inr (hc2.resolve_left h12)⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨h2D, h2S, Or.inl (hc1.resolve_left h11)⟩))
        · have h2S : e.2 ∈ S := by_contra fun h => h1S (hbi.mpr h)
          by_cases h21 : e.2 ∈ C1
          · by_cases h22 : e.2 ∈ C2
            · exact Or.inr (Or.inr (Or.inl ⟨h2D, h2S, h21, h22⟩))
            · exact Or.inl (Or.inr (Or.inr ⟨h1D, h1S, Or.inr (hc2.resolve_right h22)⟩))
          · exact Or.inl (Or.inr (Or.inr ⟨h1D, h1S, Or.inl (hc1.resolve_right h21)⟩))
  have hJ_cov : ∀ e ∈ G, e.1 ∈ J ∨ e.2 ∈ J := by
    intro e he
    have hc1 := h1.1 e he
    have hc2 := h2.1 e he
    rw [hJ_mem e.1, hJ_mem e.2]
    by_cases h1D : e.1 ∈ D
    · by_cases h11 : e.1 ∈ C1
      · exact Or.inl (Or.inl ⟨h1D, h11⟩)
      · have h12 : e.1 ∉ C2 := fun h => h11 ((hD_iff e.1 h1D).mpr h)
        have h21 : e.2 ∈ C1 := hc1.resolve_left h11
        have h22 : e.2 ∈ C2 := hc2.resolve_left h12
        by_cases h2D : e.2 ∈ D
        · exact Or.inr (Or.inl ⟨h2D, h21⟩)
        · by_cases h2S : e.2 ∈ S
          · exact Or.inr (Or.inr (Or.inl ⟨h2D, h2S, Or.inl h21⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨h2D, h2S, h21, h22⟩))
    · by_cases h2D : e.2 ∈ D
      · by_cases h21 : e.2 ∈ C1
        · exact Or.inr (Or.inl ⟨h2D, h21⟩)
        · have h22 : e.2 ∉ C2 := fun h => h21 ((hD_iff e.2 h2D).mpr h)
          have h11 : e.1 ∈ C1 := hc1.resolve_right h21
          have h12 : e.1 ∈ C2 := hc2.resolve_right h22
          by_cases h1S : e.1 ∈ S
          · exact Or.inl (Or.inr (Or.inl ⟨h1D, h1S, Or.inl h11⟩))
          · exact Or.inl (Or.inr (Or.inr ⟨h1D, h1S, h11, h12⟩))
      · have hbi := hbip e he h1D h2D
        by_cases h1S : e.1 ∈ S
        · have h2S : e.2 ∉ S := hbi.mp h1S
          by_cases h21 : e.2 ∈ C1
          · by_cases h22 : e.2 ∈ C2
            · exact Or.inr (Or.inr (Or.inr ⟨h2D, h2S, h21, h22⟩))
            · exact Or.inl (Or.inr (Or.inl ⟨h1D, h1S, Or.inr (hc2.resolve_right h22)⟩))
          · exact Or.inl (Or.inr (Or.inl ⟨h1D, h1S, Or.inl (hc1.resolve_right h21)⟩))
        · have h2S : e.2 ∈ S := by_contra fun h => h1S (hbi.mpr h)
          by_cases h11 : e.1 ∈ C1
          · by_cases h12 : e.1 ∈ C2
            · exact Or.inl (Or.inr (Or.inr ⟨h1D, h1S, h11, h12⟩))
            · exact Or.inr (Or.inr (Or.inl ⟨h2D, h2S, Or.inr (hc2.resolve_left h12)⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨h2D, h2S, Or.inl (hc1.resolve_left h11)⟩))
  have hsum : M.sum w + J.sum w = C1.sum w + C2.sum w := by
    have hrewrite : ∀ A : Finset (Fin N), A.sum w = ∑ x : Fin N, if x ∈ A then w x else 0 := fun A => by
      rw [← Finset.sum_filter]
      congr 1; ext x; simp
    rw [hrewrite M, hrewrite J, hrewrite C1, hrewrite C2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hxD : x ∈ D
    · have hiff := hD_iff x hxD
      by_cases ha : x ∈ C1
      · have hb : x ∈ C2 := hiff.mp ha
        have hm : x ∈ M := (hM_mem x).mpr (Or.inl ⟨hxD, ha⟩)
        have hj : x ∈ J := (hJ_mem x).mpr (Or.inl ⟨hxD, ha⟩)
        simp only [hm, hj, ha, hb, ↓reduceIte]
      · have hb : x ∉ C2 := fun h => ha (hiff.mpr h)
        have hm : x ∉ M := fun h => by rw [hM_mem] at h; tauto
        have hj : x ∉ J := fun h => by rw [hJ_mem] at h; tauto
        simp only [hm, hj, ha, hb, ↓reduceIte]
    · by_cases hxS : x ∈ S
      · by_cases ha : x ∈ C1 <;> by_cases hb : x ∈ C2
        · have hm : x ∈ M := (hM_mem x).mpr (Or.inr (Or.inl ⟨hxD, hxS, ha, hb⟩))
          have hj : x ∈ J := (hJ_mem x).mpr (Or.inr (Or.inl ⟨hxD, hxS, Or.inl ha⟩))
          simp only [hm, hj, ha, hb, ↓reduceIte]
        · have hm : x ∉ M := fun h => by rw [hM_mem] at h; tauto
          have hj : x ∈ J := (hJ_mem x).mpr (Or.inr (Or.inl ⟨hxD, hxS, Or.inl ha⟩))
          simp only [hm, hj, ha, hb, ↓reduceIte, zero_add, add_zero]
        · have hm : x ∉ M := fun h => by rw [hM_mem] at h; tauto
          have hj : x ∈ J := (hJ_mem x).mpr (Or.inr (Or.inl ⟨hxD, hxS, Or.inr hb⟩))
          simp only [hm, hj, ha, hb, ↓reduceIte, zero_add, add_zero]
        · have hm : x ∉ M := fun h => by rw [hM_mem] at h; tauto
          have hj : x ∉ J := fun h => by rw [hJ_mem] at h; tauto
          simp only [hm, hj, ha, hb, ↓reduceIte]
      · by_cases ha : x ∈ C1 <;> by_cases hb : x ∈ C2
        · have hm : x ∈ M := (hM_mem x).mpr (Or.inr (Or.inr ⟨hxD, hxS, Or.inl ha⟩))
          have hj : x ∈ J := (hJ_mem x).mpr (Or.inr (Or.inr ⟨hxD, hxS, ha, hb⟩))
          simp only [hm, hj, ha, hb, ↓reduceIte]
        · have hm : x ∈ M := (hM_mem x).mpr (Or.inr (Or.inr ⟨hxD, hxS, Or.inl ha⟩))
          have hj : x ∉ J := fun h => by rw [hJ_mem] at h; tauto
          simp only [hm, hj, ha, hb, ↓reduceIte, add_zero]
        · have hm : x ∈ M := (hM_mem x).mpr (Or.inr (Or.inr ⟨hxD, hxS, Or.inr hb⟩))
          have hj : x ∉ J := fun h => by rw [hJ_mem] at h; tauto
          simp only [hm, hj, ha, hb, ↓reduceIte, zero_add, add_zero]
        · have hm : x ∉ M := fun h => by rw [hM_mem] at h; tauto
          have hj : x ∉ J := fun h => by rw [hJ_mem] at h; tauto
          simp only [hm, hj, ha, hb, ↓reduceIte]
  have hM_le : M.sum w ≤ C1.sum w := by
    have ha := h1.2 M hM_cov
    have hb := h2.2 J hJ_cov
    omega
  have hJ_le : J.sum w ≤ C2.sum w := by
    have ha := h1.2 M hM_cov
    have hb := h2.2 J hJ_cov
    omega
  refine ⟨M, J, hM_mem, hJ_mem,
    ⟨hM_cov, fun B hB => le_trans hM_le (h1.2 B hB)⟩,
    ⟨hJ_cov, fun B hB => le_trans hJ_le (h2.2 B hB)⟩,
    ⟨fun x hx => by
      simp only [Finset.mem_inter] at hx
      rw [hM_mem]; by_cases hxD : x ∈ D <;> by_cases hxS : x ∈ S <;> tauto,
     fun x hx => by
      rw [hM_mem] at hx; simp only [Finset.mem_union]; tauto⟩,
    ⟨fun x hx => by
      simp only [Finset.mem_inter] at hx
      rw [hJ_mem]; by_cases hxD : x ∈ D <;> by_cases hxS : x ∈ S <;> tauto,
     fun x hx => by
      rw [hJ_mem] at hx; simp only [Finset.mem_union]; tauto⟩⟩

lemma part1_lower_bound {m N : Nat}
    (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (p : Fin m × Fin 3 → Fin N)
    (D S I O : Finset (Fin N))
    (hbip : ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S))
    (hR : ∀ X : Finset (Fin m × Fin 3),
      (∀ i : Fin m, ∃ j : Fin 3, (i, j) ∈ X) ↔
      ∃ C : Finset (Fin N),
        ((∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧ ∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C.sum w ≤ B.sum w) ∧
        I ⊆ C ∧ Disjoint O C ∧ Finset.univ.filter (fun v : Fin m × Fin 3 => p v ∈ C) = X) :
    m ≤ D.card := by
  classical
  have hpair : ∀ i : Fin m, ∃ a b : Fin 3, a ≠ b ∧ (p (i, a) ∈ S ↔ p (i, b) ∈ S) := by
    intro i
    by_cases h0 : p (i, 0) ∈ S
    · by_cases h1 : p (i, 1) ∈ S
      · exact ⟨0, 1, by decide, by simp [h0, h1]⟩
      · by_cases h2 : p (i, 2) ∈ S
        · exact ⟨0, 2, by decide, by simp [h0, h2]⟩
        · exact ⟨1, 2, by decide, by simp [h1, h2]⟩
    · by_cases h1 : p (i, 1) ∈ S
      · by_cases h2 : p (i, 2) ∈ S
        · exact ⟨1, 2, by decide, by simp [h1, h2]⟩
        · exact ⟨0, 2, by decide, by simp [h0, h2]⟩
      · exact ⟨0, 1, by decide, by simp [h0, h1]⟩
  choose a b hab hsame using hpair
  have hword : ∀ f : Fin m → Bool,
      ∃ C : Finset (Fin N),
        ((∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧ ∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C.sum w ≤ B.sum w) ∧
        I ⊆ C ∧ Disjoint O C ∧
        Finset.univ.filter (fun v : Fin m × Fin 3 => p v ∈ C) =
          Finset.univ.image (fun i : Fin m => (i, if f i then a i else b i)) := by
    intro f
    apply (hR _).mp
    intro i
    exact ⟨if f i then a i else b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  choose Cf hCf_opt hCf_I hCf_O hCf_sig using hword
  have hinj : Function.Injective (fun f : Fin m → Bool => Cf f ∩ D) := by
    intro f1 f2 heq
    by_contra hne
    have hne_i : ∃ i : Fin m, f1 i ≠ f2 i := by
      by_contra hall
      push_neg at hall
      exact hne (funext hall)
    obtain ⟨i, hi⟩ := hne_i
    let C1 := Cf f1
    let C2 := Cf f2
    have hD_iff : ∀ x ∈ D, x ∈ C1 ↔ x ∈ C2 := by
      intro x hxD
      have h1 : x ∈ C1 ∩ D ↔ x ∈ C2 ∩ D := by rw [show C1 ∩ D = C2 ∩ D from heq]
      simp [hxD] at h1
      exact h1
    obtain ⟨M, J, hM_mem, hJ_mem, hM_opt, hJ_opt, hsub_M, hsub_J⟩ :=
      bipartite_MJ G w D S C1 C2 hbip (hCf_opt f1) (hCf_opt f2) heq
    have hRM : ∀ k : Fin m, ∃ j : Fin 3, (k, j) ∈ Finset.univ.filter (fun v : Fin m × Fin 3 => p v ∈ M) :=
      (hR _).mpr ⟨M, hM_opt,
        Finset.Subset.trans (Finset.subset_inter (hCf_I f1) (hCf_I f2)) hsub_M.1,
        Finset.disjoint_of_subset_right hsub_M.2 (Finset.disjoint_union_right.mpr ⟨hCf_O f1, hCf_O f2⟩),
        rfl⟩
    have hRJ : ∀ k : Fin m, ∃ j : Fin 3, (k, j) ∈ Finset.univ.filter (fun v : Fin m × Fin 3 => p v ∈ J) :=
      (hR _).mpr ⟨J, hJ_opt,
        Finset.Subset.trans (Finset.subset_inter (hCf_I f1) (hCf_I f2)) hsub_J.1,
        Finset.disjoint_of_subset_right hsub_J.2 (Finset.disjoint_union_right.mpr ⟨hCf_O f1, hCf_O f2⟩),
        rfl⟩
    have hmem1 : ∀ j : Fin 3, p (i, j) ∈ C1 ↔ j = if f1 i then a i else b i := by
      intro j
      have h : (i, j) ∈ Finset.univ.filter (fun v : Fin m × Fin 3 => p v ∈ C1) ↔
          (i, j) ∈ Finset.univ.image (fun k : Fin m => (k, if f1 k then a k else b k)) := by
        rw [show Finset.univ.filter (fun v : Fin m × Fin 3 => p v ∈ C1) = _ from hCf_sig f1]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq] at h
      constructor
      · intro hp; obtain ⟨k, rfl, hkj⟩ := h.mp hp; exact hkj.symm
      · intro hj; exact h.mpr ⟨i, rfl, hj.symm⟩
    have hmem2 : ∀ j : Fin 3, p (i, j) ∈ C2 ↔ j = if f2 i then a i else b i := by
      intro j
      have h : (i, j) ∈ Finset.univ.filter (fun v : Fin m × Fin 3 => p v ∈ C2) ↔
          (i, j) ∈ Finset.univ.image (fun k : Fin m => (k, if f2 k then a k else b k)) := by
        rw [show Finset.univ.filter (fun v : Fin m × Fin 3 => p v ∈ C2) = _ from hCf_sig f2]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq] at h
      constructor
      · intro hp; obtain ⟨k, rfl, hkj⟩ := h.mp hp; exact hkj.symm
      · intro hj; exact h.mpr ⟨i, rfl, hj.symm⟩
    have hdisj_c12 : ∀ j : Fin 3, ¬ (p (i, j) ∈ C1 ∧ p (i, j) ∈ C2) := by
      intro j ⟨h1, h2⟩
      rw [hmem1 j] at h1
      rw [hmem2 j] at h2
      have hEq : (if f1 i then a i else b i) = (if f2 i then a i else b i) := h1.symm.trans h2
      cases hf1 : f1 i <;> cases hf2 : f2 i
      · exact hi (hf1.trans hf2.symm)
      · rw [hf1, hf2] at hEq; simp at hEq; exact hab i hEq.symm
      · rw [hf1, hf2] at hEq; simp at hEq; exact hab i hEq
      · exact hi (hf1.trans hf2.symm)
    have hnotD : ∀ j : Fin 3, p (i, j) ∈ C1 ∨ p (i, j) ∈ C2 → p (i, j) ∉ D := by
      intro j h12 hD
      rcases h12 with h1 | h2
      · exact hdisj_c12 j ⟨h1, (hD_iff _ hD).mp h1⟩
      · exact hdisj_c12 j ⟨(hD_iff _ hD).mpr h2, h2⟩
    by_cases haS : p (i, a i) ∈ S
    · have hbS : p (i, b i) ∈ S := (hsame i).mp haS
      obtain ⟨j, hj⟩ := hRM i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hj12 : p (i, j) ∈ C1 ∨ p (i, j) ∈ C2 := Finset.mem_union.mp (hsub_M.2 hj)
      have hjD : p (i, j) ∉ D := hnotD j hj12
      have hjS : p (i, j) ∈ S := by
        rcases hj12 with h1 | h2
        · rw [hmem1 j] at h1; rw [h1]; split_ifs <;> assumption
        · rw [hmem2 j] at h2; rw [h2]; split_ifs <;> assumption
      rw [hM_mem] at hj
      rcases hj with ⟨hD, _⟩ | ⟨_, _, h12⟩ | ⟨_, hS, _⟩
      · exact hjD hD
      · exact hdisj_c12 j h12
      · exact hS hjS
    · have hbS : p (i, b i) ∉ S := fun h => haS ((hsame i).mpr h)
      obtain ⟨j, hj⟩ := hRJ i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hj12 : p (i, j) ∈ C1 ∨ p (i, j) ∈ C2 := Finset.mem_union.mp (hsub_J.2 hj)
      have hjD : p (i, j) ∉ D := hnotD j hj12
      have hjS : p (i, j) ∉ S := by
        rcases hj12 with h1 | h2
        · rw [hmem1 j] at h1; rw [h1]; split_ifs <;> assumption
        · rw [hmem2 j] at h2; rw [h2]; split_ifs <;> assumption
      rw [hJ_mem] at hj
      rcases hj with ⟨hD, _⟩ | ⟨_, hS, _⟩ | ⟨_, _, h12⟩
      · exact hjD hD
      · exact hjS hS
      · exact hdisj_c12 j h12
  have hcard : Fintype.card (Fin m → Bool) ≤ D.powerset.card := by
    have hmap : (Finset.univ.image (fun f : Fin m → Bool => Cf f ∩ D)).card ≤ D.powerset.card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_powerset.mpr Finset.inter_subset_right
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ] at hmap
    exact hmap
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Finset.card_powerset] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

end PEqualNP.Outside.L_lib_1500_aux

theorem PEqualNP.Outside.L_lib_1500 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let cover := fun {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
let opt := fun {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (C : Finset (Fin N)) =>
  cover G C ∧ ∀ B, cover G B → C.sum w ≤ B.sum w
let bip := fun {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
let view := fun {k N : Nat} (p : Fin k → Fin N) (C : Finset (Fin N)) =>
  Finset.univ.filter (fun i => p i ∈ C)
let simple := fun {N : Nat} (G : Finset (Fin N × Fin N)) (b : Nat) =>
  (∀ e ∈ G, e.1 < e.2) ∧ ∀ u : Fin N, (G.filter (fun e => u=e.1 ∨ u=e.2)).card ≤ b
∀ m : Nat,
let V := Fin m × Fin 3
let R := fun (X : Finset V) => ∀ i : Fin m, ∃ j : Fin 3, (i,j) ∈ X
let sig := fun {N : Nat} (p : V → Fin N) (C : Finset (Fin N)) =>
  Finset.univ.filter (fun v : V => p v ∈ C)
(∀ (N : Nat) (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (p : V → Fin N)
  (D S I O : Finset (Fin N)), bip G D S →
  (∀ X, R X ↔ ∃ C, opt G w C ∧ I ⊆ C ∧ Disjoint O C ∧ sig p C=X) → m ≤ D.card) ∧
∃ (G : Finset (Fin (9*m) × Fin (9*m))) (p : V → Fin (9*m)) (D S : Finset (Fin (9*m))),
  simple G 5 ∧ Function.Injective p ∧ D.card=m ∧ bip G D S ∧
  (∀ C, cover G C → 5*m ≤ C.card) ∧
  (∀ X, R X ↔ ∃ C, cover G C ∧ C.card=5*m ∧ sig p C=X) ∧
  ∀ C B, cover G C → cover G B → C.card=5*m → B.card=5*m → sig p C=sig p B → C=B) := by
  intro cover opt bip view simple m V R sig
  open PEqualNP.Outside.L_lib_1500_aux in
  constructor
  · intro N G w p D S I O hbip hR
    apply part1_lower_bound G w p D S I O hbip
    intro X
    dsimp only [R, opt, cover, sig] at hR
    rw [hR X]
    constructor
    · rintro ⟨C, hopt, hI, hO, hsig⟩
      exact ⟨C, hopt, hI, hO, by convert hsig⟩
    · rintro ⟨C, hopt, hI, hO, hsig⟩
      exact ⟨C, hopt, hI, hO, by convert hsig⟩
  · let G : Finset (Fin (9 * m) × Fin (9 * m)) :=
      (Finset.univ (α := Fin m) ×ˢ HEdges).image (fun x => (equiv9 m (x.1, x.2.1), equiv9 m (x.1, x.2.2)))
    let p : V → Fin (9 * m) := fun v => equiv9 m (v.1, ⟨v.2.val, by omega⟩)
    let D : Finset (Fin (9 * m)) := Finset.univ.image (fun i : Fin m => equiv9 m (i, 8))
    let S : Finset (Fin (9 * m)) := Finset.univ.filter (fun u : Fin (9 * m) => (equiv9 m |>.symm u).2 ∈ SH)
    have hcov_iff : ∀ C : Finset (Fin (9 * m)), cover G C ↔ ∀ i : Fin m, coverH (slice9 C i) := by
      intro C
      constructor
      · intro hC i e he
        have heG : (equiv9 m (i, e.1), equiv9 m (i, e.2)) ∈ G :=
          Finset.mem_image.mpr ⟨(i, e), Finset.mem_product.mpr ⟨Finset.mem_univ i, he⟩, rfl⟩
        rcases hC _ heG with h1 | h2
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
      · intro hC e heG
        obtain ⟨⟨i, e0⟩, hmem, rfl⟩ := Finset.mem_image.mp heG
        have he0 : e0 ∈ HEdges := (Finset.mem_product.mp hmem).2
        rcases hC i e0 he0 with h1 | h2
        · exact Or.inl (Finset.mem_filter.mp h1).2
        · exact Or.inr (Finset.mem_filter.mp h2).2
    have hmin_all : ∀ C : Finset (Fin (9 * m)), cover G C → 5 * m ≤ C.card := by
      intro C hC
      rw [card_eq_sum_slice9 C]
      calc 5 * m = ∑ _i : Fin m, 5 := by simp [mul_comm]
        _ ≤ ∑ i : Fin m, (slice9 C i).card :=
          Finset.sum_le_sum fun i _ => H_min_vc (slice9 C i) ((hcov_iff C).mp hC i)
    have hcard5_all : ∀ C : Finset (Fin (9 * m)), cover G C → C.card = 5 * m →
        ∀ i : Fin m, (slice9 C i).card = 5 := by
      intro C hC hcard
      rw [card_eq_sum_slice9 C] at hcard
      have hsum_eq : ∑ _i : Fin m, 5 = ∑ i : Fin m, (slice9 C i).card := by
        rw [hcard]; simp [mul_comm]
      have hle : ∀ i ∈ (Finset.univ : Finset (Fin m)), 5 ≤ (slice9 C i).card := fun i _ =>
        H_min_vc (slice9 C i) ((hcov_iff C).mp hC i)
      intro i
      exact ((Finset.sum_eq_sum_iff_of_le hle).mp hsum_eq i (Finset.mem_univ i)).symm
    have hsig_slice : ∀ (C : Finset (Fin (9 * m))) (i : Fin m) (j : Fin 3),
        (i, j) ∈ sig p C ↔ j ∈ sigH (slice9 C i) := by
      intro C i j
      simp [sig, sigH, slice9, p]
    refine ⟨G, p, D, S, ?_, ?_, ?_, ?_, hmin_all, ?_, ?_⟩
    · constructor
      · intro e he
        obtain ⟨⟨i, e0⟩, hmem, rfl⟩ := Finset.mem_image.mp he
        have he0 : e0 ∈ HEdges := (Finset.mem_product.mp hmem).2
        have hlt := H_lt e0 he0
        change 9 * i.val + e0.1.val < 9 * i.val + e0.2.val
        omega
      · intro u
        let i0 := (equiv9 m).symm u |>.1
        let r0 := (equiv9 m).symm u |>.2
        have hu : u = equiv9 m (i0, r0) := ((equiv9 m).apply_symm_apply u).symm
        let f : Fin 9 × Fin 9 → Fin (9 * m) × Fin (9 * m) :=
          fun e0 => (equiv9 m (i0, e0.1), equiv9 m (i0, e0.2))
        have hsub : G.filter (fun e => u = e.1 ∨ u = e.2) ⊆
            (HEdges.filter (fun e0 => r0 = e0.1 ∨ r0 = e0.2)).image f := by
          intro e he
          simp only [Finset.mem_filter] at he
          obtain ⟨heG, hu12⟩ := he
          obtain ⟨⟨i, e0⟩, hmem, rfl⟩ := Finset.mem_image.mp heG
          have he0 : e0 ∈ HEdges := (Finset.mem_product.mp hmem).2
          rcases hu12 with h1 | h2
          · have heq := (equiv9 m).injective (hu.symm.trans h1)
            have hi : i = i0 := (Prod.mk.inj heq).1.symm
            have hr : r0 = e0.1 := (Prod.mk.inj heq).2
            subst hi
            exact Finset.mem_image.mpr ⟨e0, Finset.mem_filter.mpr ⟨he0, Or.inl hr⟩, rfl⟩
          · have heq := (equiv9 m).injective (hu.symm.trans h2)
            have hi : i = i0 := (Prod.mk.inj heq).1.symm
            have hr : r0 = e0.2 := (Prod.mk.inj heq).2
            subst hi
            exact Finset.mem_image.mpr ⟨e0, Finset.mem_filter.mpr ⟨he0, Or.inr hr⟩, rfl⟩
        have hle1 : (G.filter (fun e => u = e.1 ∨ u = e.2)).card ≤
            ((HEdges.filter (fun e0 => r0 = e0.1 ∨ r0 = e0.2)).image f).card := Finset.card_le_card hsub
        have hle2 : ((HEdges.filter (fun e0 => r0 = e0.1 ∨ r0 = e0.2)).image f).card ≤ 5 :=
          le_trans Finset.card_image_le (H_deg r0)
        exact le_trans (by convert hle1) hle2
    · intro v1 v2 heq
      have h := (equiv9 m).injective heq
      have h1 : v1.1 = v2.1 := (Prod.mk.inj h).1
      have h2 : v1.2 = v2.2 := Fin.ext (by simpa using congrArg Fin.val (Prod.mk.inj h).2)
      exact Prod.ext h1 h2
    · have hinjD : Function.Injective (fun i : Fin m => equiv9 m (i, 8)) := by
        intro i1 i2 heq
        exact (Prod.mk.inj ((equiv9 m).injective heq)).1
      rw [Finset.card_image_of_injective _ hinjD, Finset.card_univ, Fintype.card_fin]
    · intro e he h1D h2D
      obtain ⟨⟨i, e0⟩, hmem, rfl⟩ := Finset.mem_image.mp he
      have he0 : e0 ∈ HEdges := (Finset.mem_product.mp hmem).2
      have h1ne : e0.1 ≠ 8 := fun h => h1D (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, by rw [h]⟩)
      have h2ne : e0.2 ≠ 8 := fun h => h2D (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, by rw [h]⟩)
      have hbi := H_bip e0 he0 h1ne h2ne
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
      exact hbi
    · intro X
      constructor
      · intro hRX
        let Xi : Fin m → Finset (Fin 3) := fun i => Finset.univ.filter (fun j : Fin 3 => (i, j) ∈ X)
        have hXi_ne : ∀ i : Fin m, (Xi i).Nonempty := fun i => by
          obtain ⟨j, hj⟩ := hRX i
          exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
        let C : Finset (Fin (9 * m)) :=
          Finset.univ.filter (fun u : Fin (9 * m) => (equiv9 m |>.symm u).2 ∈ vcH (Xi (equiv9 m |>.symm u |>.1)))
        have hsliceC : ∀ i : Fin m, slice9 C i = vcH (Xi i) := by
          intro i; ext r
          simp [slice9, C]
        refine ⟨C, ?_, ?_, ?_⟩
        · exact (hcov_iff C).mpr fun i => by rw [hsliceC i]; exact (H_vcH_spec (Xi i) (hXi_ne i)).1
        · rw [card_eq_sum_slice9 C]
          have hsum : ∑ i : Fin m, (slice9 C i).card = ∑ _i : Fin m, 5 := by
            apply Finset.sum_congr rfl; intro i _
            rw [hsliceC i]; exact (H_vcH_spec (Xi i) (hXi_ne i)).2.1
          rw [hsum]; simp [mul_comm]
        · ext ⟨i, j⟩
          rw [hsig_slice C i j, hsliceC i, (H_vcH_spec (Xi i) (hXi_ne i)).2.2]
          simp [Xi]
      · rintro ⟨C, hC, hcard, hsig⟩ i
        have h5 := hcard5_all C hC hcard i
        have hne := (H_eq_vcH (slice9 C i) ((hcov_iff C).mp hC i) h5).1
        obtain ⟨j, hj⟩ := hne
        exact ⟨j, by rw [← hsig]; exact (hsig_slice C i j).mpr hj⟩
    · intro C B hC hB hCcard hBcard hsig
      have hC5 := hcard5_all C hC hCcard
      have hB5 := hcard5_all B hB hBcard
      have hslice_eq : ∀ i : Fin m, slice9 C i = slice9 B i := by
        intro i
        have hsig_i : sigH (slice9 C i) = sigH (slice9 B i) := by
          ext j
          rw [← hsig_slice C i j, ← hsig_slice B i j, hsig]
        rw [(H_eq_vcH (slice9 C i) ((hcov_iff C).mp hC i) (hC5 i)).2,
            (H_eq_vcH (slice9 B i) ((hcov_iff B).mp hB i) (hB5 i)).2, hsig_i]
      ext u
      have hu : u = equiv9 m ((equiv9 m).symm u) := ((equiv9 m).apply_symm_apply u).symm
      have hmem : ∀ A : Finset (Fin (9 * m)), u ∈ A ↔ ((equiv9 m).symm u).2 ∈ slice9 A ((equiv9 m).symm u).1 := by
        intro A
        simp only [slice9, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.eta, Equiv.apply_symm_apply]
      rw [hmem C, hmem B, hslice_eq]
