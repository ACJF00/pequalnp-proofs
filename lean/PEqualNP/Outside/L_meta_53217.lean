import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Helpers.GraphSampleDistance

namespace PEqualNP.Outside.L_meta_53217

section Crit
open Classical PEqualNP GraphInversionSeeds GraphSampleDistance

theorem valCrit {n c : ℕ} (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c)
    (onto : Function.Surjective color) (sorted : ∀ e ∈ E, e.1 < e.2)
    (part : ∀ V : Finset (Fin n), (∀ e∈E, e.1∈V ↔ e.2∈V) ↔
      ∀ i k, color i=color k → (i∈V ↔ k∈V))
    (w : Finset (Fin n) → ℕ) (D : ℕ) (hD : 0 < D) :
    (∀ lost : Finset (Fin n) → ℕ, (∑ x, lost x) < D →
      keeps (Finset.univ.filter (fun x => lost x < w x)) E color) ↔
    (∀ j, D ≤ (Finset.univ.filter (fun u => Disjoint u (GraphSeedSamples.block color j))).sum
        (fun u => min (w u) (w (u ∪ GraphSeedSamples.block color j)))) ∧
    (∀ f ∈ target E, ∀ g ∈ target E, f ≠ g → D ≤ margin Finset.univ w f g) ∧
    (∀ f ∈ target E, ∀ g ∈ raw E, D ≤ margin Finset.univ w f g) := by
  set A := Finset.univ.filter (fun x : Finset (Fin n) => 0 < w x) with hA
  have pos : ∀ u ∈ A, 0 < w u := fun u hu => by simpa [hA] using hu
  have cr := GraphSampleDistance.criterion n c E color onto sorted part A w (D-1) pos
  have lhs : (∀ lost : Finset (Fin n) → ℕ, (∑ x, lost x) < D →
      keeps (Finset.univ.filter (fun x => lost x < w x)) E color) ↔
      (∀ lost : Finset (Fin n) → ℕ, A.sum lost ≤ D-1 →
        keeps (A.filter (fun u => lost u < w u)) E color) := by
    have fe : ∀ lost : Finset (Fin n) → ℕ, A.filter (fun u => lost u < w u) =
        Finset.univ.filter (fun x => lost x < w x) := by
      intro lost; ext x; simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    constructor
    · intro h lost hl
      rw [fe]
      have e2 : Finset.univ.filter (fun x => lost x < w x) =
          Finset.univ.filter (fun x => (if x ∈ A then lost x else 0) < w x) := by
        ext x; by_cases hx : x ∈ A
        · simp [hx]
        · have : w x = 0 := by simpa [hA] using hx
          simp [hx, this]
      rw [e2]
      apply h
      rw [← Finset.sum_filter]
      have : Finset.univ.filter (fun x => x ∈ A) = A := by ext; simp
      rw [this]
      have hl' : (∑ a ∈ A, lost a) ≤ D - 1 := hl
      omega
    · intro h lost hl
      rw [← fe]
      apply h
      have := Finset.sum_le_sum_of_subset (f := lost) (Finset.subset_univ A)
      change (∑ a ∈ A, lost a) ≤ D - 1
      omega
  rw [lhs]
  refine cr.trans ?_
  have m : ∀ f g : F n, margin A w f g = margin Finset.univ w f g := by
    intro f g
    unfold margin
    apply Finset.sum_subset
    · intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_univ _, hx.2⟩
    · intro x hx hx'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, hA] at hx hx'
      by_contra hw
      exact hx' (Nat.pos_of_ne_zero hw) hx
  have l : ∀ j, (lows A (GraphSeedSamples.block color j)).sum
      (fun u => min (w u) (w (u ∪ GraphSeedSamples.block color j))) =
      (Finset.univ.filter (fun u => Disjoint u (GraphSeedSamples.block color j))).sum
        (fun u => min (w u) (w (u ∪ GraphSeedSamples.block color j))) := by
    intro j
    apply Finset.sum_subset
    · intro x hx; simp only [lows, Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_univ _, hx.2.1⟩
    · intro x hx hx'
      simp only [lows, Finset.mem_filter, Finset.mem_univ, true_and, not_and, hA] at hx hx'
      by_cases h1 : 0 < w x
      · have : ¬ 0 < w (x ∪ GraphSeedSamples.block color j) := hx' h1 hx
        simp [Nat.eq_zero_of_not_pos this]
      · simp [Nat.eq_zero_of_not_pos h1]
  change ((∀ j, D-1 < (lows A (GraphSeedSamples.block color j)).sum
      (fun u => min (w u) (w (u ∪ GraphSeedSamples.block color j)))) ∧
    (∀ f ∈ target E, ∀ g ∈ target E, f ≠ g → D-1 < margin A w f g) ∧
    (∀ f ∈ target E, ∀ g ∈ raw E, D-1 < margin A w f g)) ↔ _
  simp only [l, m]
  have e : ∀ x, D - 1 < x ↔ D ≤ x := fun x => by omega
  simp only [e]

end Crit


section Core

variable {n c : ℕ} [inst : ∀ Q : Prop, Decidable Q]

def cp (color : Fin n → Fin c) (j : Fin c) : Finset (Fin n) :=
  Finset.univ.filter (fun i => color i = j)

def nm (color : Fin n → Fin c) (x : Finset (Fin n)) : Finset (Fin n) :=
  x.filter (fun i => ¬ cp color (color i) ⊆ x)

theorem mem_cp (color : Fin n → Fin c) (i : Fin n) (j : Fin c) :
    i ∈ cp color j ↔ color i = j := by
  simp [cp]

theorem cp_disj (color : Fin n → Fin c) (j j' : Fin c) (h : j ≠ j') :
    Disjoint (cp color j) (cp color j') := by
  rw [Finset.disjoint_left]
  intro i h1 h2
  exact h (((mem_cp _ _ _).1 h1).symm.trans ((mem_cp _ _ _).1 h2))

theorem nm_sub (color : Fin n → Fin c) (x : Finset (Fin n)) : nm color x ⊆ x :=
  Finset.filter_subset _ _

theorem nm_union (color : Fin n → Fin c) (u : Finset (Fin n)) (j : Fin c)
    (h : Disjoint u (cp color j)) : nm color (u ∪ cp color j) = nm color u := by
  ext i
  simp only [nm, Finset.mem_filter, Finset.mem_union]
  by_cases hi : color i = j
  · have h1 : i ∈ cp color j := (mem_cp _ _ _).2 hi
    have hu : i ∉ u := fun h' => Finset.disjoint_left.1 h h' h1
    have h2 : cp color (color i) ⊆ u ∪ cp color j := by
      rw [hi]; exact Finset.subset_union_right
    simp [hu, h2]
  · have hi' : i ∉ cp color j := fun h' => hi ((mem_cp _ _ _).1 h')
    have key : cp color (color i) ⊆ u ∪ cp color j ↔ cp color (color i) ⊆ u := by
      constructor
      · intro hs k hk
        rcases Finset.mem_union.1 (hs hk) with h1 | h1
        · exact h1
        · exact absurd (((mem_cp _ _ _).1 hk).symm.trans ((mem_cp _ _ _).1 h1)) hi
      · intro hs; exact hs.trans Finset.subset_union_left
    simp [hi', key]

theorem nm_disj (color : Fin n → Fin c) (x : Finset (Fin n)) (j : Fin c) :
    Disjoint (nm color x) (cp color j) ↔ Disjoint x (cp color j) ∨ cp color j ⊆ x := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    rw [Finset.not_disjoint_iff] at h1
    obtain ⟨i, hx, hj⟩ := h1
    have hci := (mem_cp _ _ _).1 hj
    have : i ∈ nm color x := by
      simp only [nm, Finset.mem_filter]; rw [hci]; exact ⟨hx, h2⟩
    exact Finset.disjoint_left.1 h this hj
  · rintro (h | h)
    · exact Finset.disjoint_of_subset_left (nm_sub _ _) h
    · rw [Finset.disjoint_left]
      intro i hi hj
      simp only [nm, Finset.mem_filter] at hi
      rw [(mem_cp _ _ _).1 hj] at hi
      exact hi.2 h

theorem nm_nm (color : Fin n → Fin c) (x : Finset (Fin n)) : nm color (nm color x) = nm color x := by
  ext i
  constructor
  · intro h; exact nm_sub _ _ h
  · intro h
    have h' := h
    simp only [nm, Finset.mem_filter] at h'
    exact Finset.mem_filter.2 ⟨h, fun hs => h'.2 (hs.trans (nm_sub _ _))⟩

theorem pair_sum (color : Fin n → Fin c) (j : Fin c) (hne : (cp color j).Nonempty)
    (h : Finset (Fin n) → ℕ) :
    (Finset.univ.filter (fun x => Disjoint (nm color x) (cp color j))).sum h =
      (Finset.univ.filter (fun x => Disjoint x (cp color j))).sum
        (fun u => h u + h (u ∪ cp color j)) := by
  have split : Finset.univ.filter (fun x => Disjoint (nm color x) (cp color j)) =
      Finset.univ.filter (fun x => Disjoint x (cp color j)) ∪
        Finset.univ.filter (fun x => cp color j ⊆ x) := by
    ext x; simp [nm_disj]
  have dj : Disjoint (Finset.univ.filter (fun x => Disjoint x (cp color j)))
      (Finset.univ.filter (fun x : Finset (Fin n) => cp color j ⊆ x)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨i, hi⟩ := hne
    exact Finset.disjoint_left.1 h1 (h2 hi) hi
  rw [split, Finset.sum_union dj, Finset.sum_add_distrib]
  congr 1
  symm
  apply Finset.sum_nbij' (fun u => u ∪ cp color j) (fun x => x \ cp color j)
  · intro u hu; simp
  · intro x hx; simp [Finset.sdiff_disjoint]
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp [Finset.sdiff_eq_self_of_disjoint hu]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [Finset.sdiff_union_of_subset hx]
  · intro u hu; rfl


theorem halve_step (color : Fin n → Fin c) (hne : ∀ j, (cp color j).Nonempty) (z : Finset (Fin n))
    (h : Finset (Fin n) → ℕ) (T : Finset (Fin c)) (j : Fin c) (hj : j ∉ T)
    (hz : Disjoint z (cp color j))
    (hinv : ∀ u, nm color u = z → Disjoint u (cp color j) → h (u ∪ cp color j) = h u) :
    (Finset.univ.filter (fun x => nm color x = z ∧ ∀ j' ∈ T, Disjoint x (cp color j'))).sum h =
      2 * (Finset.univ.filter (fun x => nm color x = z ∧
        ∀ j' ∈ insert j T, Disjoint x (cp color j'))).sum h := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun x => Disjoint x (cp color j))]
  have e1 : (Finset.univ.filter (fun x => nm color x = z ∧ ∀ j' ∈ T, Disjoint x (cp color j'))).filter
      (fun x => Disjoint x (cp color j)) = Finset.univ.filter (fun x => nm color x = z ∧
        ∀ j' ∈ insert j T, Disjoint x (cp color j')) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      forall_eq_or_imp]; tauto
  rw [e1, two_mul]
  congr 1
  symm
  apply Finset.sum_nbij' (fun u => u ∪ cp color j) (fun x => x \ cp color j)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      forall_eq_or_imp] at hu ⊢
    obtain ⟨h1, h2, h3⟩ := hu
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [nm_union _ _ _ h2, h1]
    · intro j' hj'
      rw [Finset.disjoint_union_left]
      exact ⟨h3 j' hj', cp_disj _ _ _ (fun e => hj (e ▸ hj'))⟩
    · rw [Finset.disjoint_union_left, not_and_or]
      right
      obtain ⟨i, hi⟩ := hne j
      exact Finset.not_disjoint_iff.2 ⟨i, hi, hi⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      forall_eq_or_imp] at hx ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    have sub : cp color j ⊆ x := by
      have := (nm_disj color x j).1 (h1 ▸ hz)
      tauto
    have hd : Disjoint (x \ cp color j) (cp color j) := Finset.sdiff_disjoint
    refine ⟨?_, hd, ?_⟩
    · rw [← h1, ← nm_union _ _ _ hd, Finset.sdiff_union_of_subset sub]
    · intro j' hj'
      exact Finset.disjoint_of_subset_left Finset.sdiff_subset (h2 j' hj')
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      forall_eq_or_imp] at hu
    simp [Finset.sdiff_eq_self_of_disjoint hu.2.1]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have sub : cp color j ⊆ x := by
      have := (nm_disj color x j).1 (hx.1.1 ▸ hz)
      tauto
    simp [Finset.sdiff_union_of_subset sub]
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      forall_eq_or_imp] at hu
    exact (hinv u hu.1 hu.2.1).symm

theorem halve (color : Fin n → Fin c) (hne : ∀ j, (cp color j).Nonempty) (z : Finset (Fin n))
    (h : Finset (Fin n) → ℕ) (T : Finset (Fin c)) (hT : ∀ j ∈ T, Disjoint z (cp color j))
    (hinv : ∀ j ∈ T, ∀ u, nm color u = z → Disjoint u (cp color j) → h (u ∪ cp color j) = h u) :
    (Finset.univ.filter (fun x => nm color x = z)).sum h =
      2 ^ T.card * (Finset.univ.filter (fun x => nm color x = z ∧
        ∀ j ∈ T, Disjoint x (cp color j))).sum h := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
    rw [ih (fun j' hj' => hT j' (Finset.mem_insert_of_mem hj'))
      (fun j' hj' => hinv j' (Finset.mem_insert_of_mem hj')),
      halve_step color hne z h T j hj (hT j (Finset.mem_insert_self _ _))
        (hinv j (Finset.mem_insert_self _ _)), Finset.card_insert_of_notMem hj, pow_succ]
    ring

theorem mem_nm (color : Fin n → Fin c) (x : Finset (Fin n)) (a : Fin n) :
    a ∈ nm color x ↔ a ∈ x ∧ ¬ cp color (color a) ⊆ x := by
  simp [nm]

def Loc (color : Fin n → Fin c) (f : Finset (Fin n) → Bool) : Prop :=
  (∃ v, ∀ x, f x = v) ∨ ∃ a b : Fin n, ∃ φ : Bool → Bool → Bool, color a = color b ∧
    ∀ x, f x = φ (decide (a ∈ x)) (decide (b ∈ x))

theorem bool_eq (p q r s : Bool) (h : ((p.toNat : ℤ) - q.toNat = r.toNat - s.toNat)) :
    (p ≠ r ↔ q ≠ s) := by
  cases p <;> cases q <;> cases r <;> cases s <;> simp_all

theorem loc_step (color : Fin n → Fin c) (f : Finset (Fin n) → Bool) (hf : Loc color f)
    (u : Finset (Fin n)) (j : Fin c) (hd : Disjoint u (cp color j)) :
    ((f (u ∪ cp color j)).toNat : ℤ) - (f u).toNat = (f (cp color j)).toNat - (f ∅).toNat := by
  rcases hf with ⟨v, hv⟩ | ⟨a, b, φ, hab, hf⟩
  · simp [hv]
  · have ha : a ∈ u → color a ≠ j := fun h e => Finset.disjoint_left.1 hd h ((mem_cp _ _ _).2 e)
    have hb : b ∈ u → color b ≠ j := fun h e => Finset.disjoint_left.1 hd h ((mem_cp _ _ _).2 e)
    rw [hf, hf, hf, hf]
    by_cases hj : color a = j
    · have hb' : color b = j := hab ▸ hj
      have ha' : a ∉ u := fun h => ha h hj
      have hb'' : b ∉ u := fun h => hb h hb'
      simp [mem_cp, hj, hb', ha', hb'']
    · have hb' : color b ≠ j := hab ▸ hj
      simp [mem_cp, hj, hb']

theorem loc_cases (color : Fin n → Fin c) (f : Finset (Fin n) → Bool) (hf : Loc color f) :
    (∀ x y, f x = f y) ∨ ∃ j0 : Fin c,
      (∀ x, ¬ cp color j0 ⊆ x → f (nm color x) = f x) ∧
      (∀ x, cp color j0 ⊆ x → f x = f (cp color j0) ∧ f (nm color x) = f ∅) ∧
      (∀ j, j ≠ j0 → f (cp color j) = f ∅) := by
  rcases hf with ⟨v, hv⟩ | ⟨a, b, φ, hab, hf⟩
  · left; intro x y; rw [hv, hv]
  · right
    refine ⟨color a, ?_, ?_, ?_⟩
    · intro x hx
      rw [hf, hf]
      simp only [mem_nm, ← hab, hx, not_false_eq_true, and_true]
    · intro x hx
      have ha : a ∈ x := hx ((mem_cp _ _ _).2 rfl)
      have hb : b ∈ x := hx ((mem_cp _ _ _).2 hab.symm)
      rw [hf, hf, hf, hf]
      simp [mem_nm, ← hab, hx, ha, hb, mem_cp]
    · intro j hj
      rw [hf, hf]
      have ha : color a ≠ j := Ne.symm hj
      have hb : color b ≠ j := hab ▸ ha
      simp [mem_cp, ha, hb]

theorem loc_norm (color : Fin n → Fin c) (hne : ∀ j, (cp color j).Nonempty)
    (f g : Finset (Fin n) → Bool) (hf : Loc color f) (hg : Loc color g)
    (hdelta : ∀ j, ((f (cp color j)).toNat : ℤ) - (f ∅).toNat =
      ((g (cp color j)).toNat : ℤ) - (g ∅).toNat) (x : Finset (Fin n)) :
    (f x ≠ g x ↔ f (nm color x) ≠ g (nm color x)) := by
  have stable : ∀ h : Finset (Fin n) → Bool, Loc color h → (∀ j, h (cp color j) = h ∅) →
      ∀ y, h (nm color y) = h y := by
    intro h hh hz y
    rcases loc_cases color h hh with hc | ⟨j0, h1, h2, h3⟩
    · exact hc _ _
    · by_cases hy : cp color j0 ⊆ y
      · rw [(h2 y hy).1, (h2 y hy).2, hz]
      · exact h1 y hy
  have zero : ∀ p q : Bool, ((p.toNat : ℤ) - q.toNat = 0) → p = q := by
    intro p q; cases p <;> cases q <;> simp
  rcases loc_cases color f hf with hcf | ⟨j0, f1, f2, f3⟩
  · have fz : ∀ j, f (cp color j) = f ∅ := fun j => hcf _ _
    have gz : ∀ j, g (cp color j) = g ∅ := fun j => zero _ _ (by rw [← hdelta j, fz j]; simp)
    rw [stable f hf fz, stable g hg gz]
  · rcases loc_cases color g hg with hcg | ⟨j1, g1, g2, g3⟩
    · have gz : ∀ j, g (cp color j) = g ∅ := fun j => hcg _ _
      have fz : ∀ j, f (cp color j) = f ∅ := fun j => zero _ _ (by rw [hdelta j, gz j]; simp)
      rw [stable f hf fz, stable g hg gz]
    · by_cases e : j0 = j1
      · subst e
        by_cases hx : cp color j0 ⊆ x
        · rw [(f2 x hx).1, (f2 x hx).2, (g2 x hx).1, (g2 x hx).2]
          exact bool_eq _ _ _ _ (hdelta j0)
        · rw [f1 x hx, g1 x hx]
      · have fz : ∀ j, f (cp color j) = f ∅ := by
          intro j
          by_cases hj : j = j0
          · subst hj
            exact zero _ _ (by rw [hdelta j, g3 j e]; simp)
          · exact f3 j hj
        have gz : ∀ j, g (cp color j) = g ∅ := by
          intro j
          by_cases hj : j = j1
          · subst hj
            exact zero _ _ (by rw [← hdelta j, f3 j (Ne.symm e)]; simp)
          · exact g3 j hj
        rw [stable f hf fz, stable g hg gz]

def up (u B : Finset (Fin n)) : Finset (Fin n) := u ∪ B

theorem fiber_sum (color : Fin n → Fin c) (P : Finset (Fin n) → Prop) (h : Finset (Fin n) → ℕ) :
    (Finset.univ.filter (fun x => P (nm color x))).sum h =
      (Finset.univ.filter P).sum (fun z => (Finset.univ.filter (fun x => nm color x = z)).sum h) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := nm color) (t := Finset.univ.filter P)
    (s := Finset.univ.filter (fun x => P (nm color x)))]
  · apply Finset.sum_congr rfl
    intro z hz
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨h ▸ hz, h⟩
  · intro x hx; simpa using hx

end Core

end PEqualNP.Outside.L_meta_53217

open Classical in
theorem PEqualNP.Outside.L_meta_53217 : (∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
  (∀ e ∈ E, e.1 < e.2) → Function.Surjective color →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
    ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    (∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p
  let valid := fun (D : Nat) (w : W → Nat) =>
    ∀ lost : W → Nat, (∑ x, lost x) < D →
      keeps (Finset.univ.filter (fun x => lost x < w x))
  let comp := fun j : Fin c => Finset.univ.filter (fun i : Fin n => color i = j)
  let norm := fun x : W => x.filter (fun i => ¬ comp (color i) ⊆ x)
  let delta := fun (f : W → Bool) (j : Fin c) =>
    ((f (comp j)).toNat : Int) - ((f ∅).toNat : Int)
  let canonMass := fun (w : W → Nat) (z : W) =>
    (Finset.univ.filter (fun x : W => norm x = z)).sum w
  let comparable := fun (f g : W → Bool) =>
    f ∈ need ∧ (g ∈ raw ∨ (g ∈ need ∧ f ≠ g)) ∧ delta f = delta g
  let dist := fun (M : W → Nat) (f g : W → Bool) =>
    (Finset.univ.filter (fun z : W => f z ≠ g z)).sum M
  let low := fun j : Fin c => Finset.univ.filter (fun x : W => Disjoint x (comp j))
  let neutral := fun (M : W → Nat) (j : Fin c) => (low j).sum M
  ∀ (M : W → Nat), (∀ z, norm z ≠ z → M z = 0) →
    ∀ (k b D : Nat), 0 < k → 2*D = k*b →
    (2^n ≤ k ∨ ∀ j, b < neutral M j →
      ((low j).filter (fun x => 0 < M (norm x))).card ≤ k*(neutral M j-b)) →
    ((∃ w : W → Nat, (∀ z, canonMass w z = k*M z) ∧ valid D w) ↔
      (∀ j, b ≤ neutral M j) ∧
      (∀ f g, comparable f g → b ≤ 2*dist M f g) ∧
      ∀ z, norm z = z →
        2^((Finset.univ.filter (fun j : Fin c => Disjoint z (comp j) ∧ neutral M j = b)).card)
          ∣ k*M z)) := by

  intro n c E color sorted onto part W bit neg same raw need keeps valid comp norm delta
    canonMass comparable dist low neutral M hM k b D hk hD hslack
  have hne : ∀ j, (L_meta_53217.cp color j).Nonempty := by
    intro j; obtain ⟨i, hi⟩ := onto j; exact ⟨i, (L_meta_53217.mem_cp _ _ _).2 hi⟩
  have valEq (i : Fin n) (x : W) (d : Decidable (i∈x)) : @decide _ d = bit i x := by
    dsimp only [bit]; congr 1
  have valN (i : Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.neg i) = neg i := by
    funext x
    dsimp only [GraphSampleDistance.asWord, GraphInversionSeeds.neg, neg]
    simp only [valEq]
  have valZ (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.zz e) =
      (fun x => neg e.1 x && neg e.2 x) := by
    funext x
    dsimp only [GraphSampleDistance.asWord, GraphInversionSeeds.zz, neg]
    simp only [valEq]
  have valO (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.oz e) =
      (fun x => bit e.1 x && neg e.2 x) := by
    funext x
    dsimp only [GraphSampleDistance.asWord, GraphInversionSeeds.oz, neg]
    simp only [valEq]
  have valT (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.zo e) =
      (fun x => neg e.1 x && bit e.2 x) := by
    funext x
    dsimp only [GraphSampleDistance.asWord, GraphInversionSeeds.zo, neg]
    simp only [valEq]
  have valP (i : Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.pos i) = bit i := by
    funext x
    dsimp only [GraphSampleDistance.asWord, GraphInversionSeeds.pos]
    simp only [valEq]
  have valQ (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.eqBit e) =
      same e := by
    funext x
    dsimp only [GraphSampleDistance.asWord, GraphInversionSeeds.eqBit, same]
    simp only [valEq]
    cases bit e.1 x <;> cases bit e.2 x <;> simp
  have valX (e : Fin n × Fin n) : GraphSampleDistance.asWord (GraphInversionSeeds.xorBit e) =
      (fun x => !(same e x)) := by
    funext x
    dsimp only [GraphSampleDistance.asWord, GraphInversionSeeds.xorBit, same]
    simp only [valEq]
    cases bit e.1 x <;> cases bit e.2 x <;> simp
  have reqEq : GraphSampleDistance.req E = need := by
    ext f
    simp only [GraphSampleDistance.req, GraphInversionSeeds.target, Finset.image_union,
      Finset.image_image, Function.comp_def, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and, need, valN, valZ, valO, valT]
  have rawEq : (GraphInversionSeeds.raw E).image GraphSampleDistance.asWord = raw := by
    ext f
    simp only [GraphInversionSeeds.raw, Finset.image_union, Finset.image_insert,
      Finset.image_singleton, Finset.image_image, Function.comp_def, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and, raw, valP, valQ, valX]
    rfl
  have sameEq (e : Fin n × Fin n) : same e = GraphSeedSamples.same e := by
    funext x; by_cases h : e.1 ∈ x <;> by_cases k : e.2 ∈ x <;>
      simp [same, bit, GraphSeedSamples.same, h, k]
  have negEq (i : Fin n) : neg i = GraphSeedSamples.inv i := by
    funext x; by_cases h : i ∈ x <;> simp [neg, bit, GraphSeedSamples.inv, h]
  have bitEq (i : Fin n) (x : W) : bit i x = GraphSeedSamples.bit i x := by
    dsimp only [bit, GraphSeedSamples.bit]; congr 1
  have keepEq (A : Finset W) : keeps A ↔ GraphSampleDistance.keeps A E color := by
    unfold keeps GraphSampleDistance.keeps
    apply forall_congr'; intro S
    apply forall_congr'; intro p
    dsimp only
    generalize hl : Finset.toList _ = actual
    have eq : actual = GraphSampleDistance.wire E S := by
      rw [← hl]
      congr 1
      ext f
      simp only [raw, GraphSeedSamples.bank, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and,
        funext (fun i => funext (bitEq i)), funext negEq, funext sameEq, GraphSeedSamples.cross]
      rfl
    rw [eq]
    simp only [GraphSampleDistance.fitsAt, reqEq, GraphSeedSamples.cover]
    rfl
  have injW : Function.Injective (GraphSampleDistance.asWord (n := n)) := by
    intro f g h
    funext x
    have := congrFun h (Finset.univ.filter (fun i => x i = true))
    have hx : (fun i => decide (i ∈ Finset.univ.filter (fun i => x i = true))) = x := by
      funext i; simp
    simpa only [GraphSampleDistance.asWord, hx] using this
  have blockEq (j : Fin c) : GraphSeedSamples.block color j = comp j := by
    ext i; simp [GraphSeedSamples.block, comp]
  have VAL : ∀ (D : ℕ) (w : W → ℕ), 0 < D → (valid D w ↔
      (∀ j, D ≤ (low j).sum (fun u => min (w u) (w (u ∪ comp j)))) ∧
      (∀ f ∈ need, ∀ g ∈ need, f ≠ g → D ≤ (Finset.univ.filter (fun x => f x ≠ g x)).sum w) ∧
      (∀ f ∈ need, ∀ g ∈ raw, D ≤ (Finset.univ.filter (fun x => f x ≠ g x)).sum w)) := by
    intro D w hD
    have h1 : valid D w ↔ ∀ lost : W → ℕ, (∑ x, lost x) < D →
        GraphSampleDistance.keeps (Finset.univ.filter (fun x => lost x < w x)) E color := by
      apply forall_congr'; intro lost; apply imp_congr_right; intro _
      rw [keepEq]
      exact Iff.of_eq (by congr 1; ext x; simp)
    rw [h1, L_meta_53217.valCrit E color onto sorted part w D hD]
    have mg : ∀ f g, GraphSampleDistance.margin Finset.univ w f g =
        (Finset.univ.filter (fun x => GraphSampleDistance.asWord f x ≠
          GraphSampleDistance.asWord g x)).sum w := by
      intro f g; unfold GraphSampleDistance.margin; congr 1
    refine and_congr ?_ (and_congr ?_ ?_)
    · apply forall_congr'; intro j
      rw [blockEq]
      exact Iff.of_eq (by congr 2; ext x; simp [low])
    · rw [← reqEq]
      constructor
      · intro h f' hf' g' hg' ne
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hf'
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hg'
        have := h f hf g hg (fun e => ne (e ▸ rfl))
        rw [mg] at this; exact this
      · intro h f hf g hg ne
        rw [mg]
        exact h _ (Finset.mem_image_of_mem _ hf) _ (Finset.mem_image_of_mem _ hg)
          (fun e => ne (injW e))
    · rw [← reqEq, ← rawEq]
      constructor
      · intro h f' hf' g' hg'
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hf'
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hg'
        have := h f hf g hg
        rw [mg] at this; exact this
      · intro h f hf g hg
        rw [mg]
        exact h _ (Finset.mem_image_of_mem _ hf) _ (Finset.mem_image_of_mem _ hg)
  have hcomp : ∀ j, comp j = L_meta_53217.cp color j := fun j => rfl
  have hnorm : ∀ x, norm x = L_meta_53217.nm color x := fun x => rfl
  have unionEq : ∀ u B : Finset (Fin n), u ∪ B = L_meta_53217.up u B := by
    intro u B; ext i; simp [L_meta_53217.up]
  have edgeColor : ∀ e ∈ E, color e.1 = color e.2 := by
    intro e he
    have := (part (Finset.univ.filter (fun i => color i = color e.1))).2
      (fun i j h => by simp [h]) e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, true_iff] at this
    exact this.symm
  have locN : ∀ f ∈ need, L_meta_53217.Loc color f := by
    intro f hf
    simp only [need, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hf
    rcases hf with ((⟨i, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
    · exact Or.inr ⟨i, i, fun p _ => !p, rfl, fun x => rfl⟩
    · exact Or.inr ⟨e.1, e.2, fun p q => !p && !q, edgeColor e he, fun x => rfl⟩
    · exact Or.inr ⟨e.1, e.2, fun p q => p && !q, edgeColor e he, fun x => rfl⟩
    · exact Or.inr ⟨e.1, e.2, fun p q => !p && q, edgeColor e he, fun x => rfl⟩
  have locR : ∀ g ∈ raw, L_meta_53217.Loc color g := by
    intro g hg
    simp only [raw, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and] at hg
    rcases hg with (((rfl | rfl) | ⟨i, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
    · exact Or.inl ⟨false, fun x => rfl⟩
    · exact Or.inl ⟨true, fun x => rfl⟩
    · exact Or.inr ⟨i, i, fun p _ => p, rfl, fun x => rfl⟩
    · refine Or.inr ⟨e.1, e.2, fun p q => decide (p = q), edgeColor e he, fun x => ?_⟩
      simp only [same, bit]
      generalize decide (e.1 ∈ x) = p
      generalize decide (e.2 ∈ x) = q
      cases p <;> cases q <;> simp
    · refine Or.inr ⟨e.1, e.2, fun p q => !decide (p = q), edgeColor e he, fun x => ?_⟩
      simp only [same, bit]
      generalize decide (e.1 ∈ x) = p
      generalize decide (e.2 ∈ x) = q
      cases p <;> cases q <;> simp
  have pairK : ∀ w : W → ℕ, (∀ z, canonMass w z = k * M z) → ∀ j,
      (low j).sum (fun u => w u + w (L_meta_53217.up u (comp j))) = k * neutral M j := by
    intro w hw j
    have e1 := L_meta_53217.pair_sum color j (hne j) w
    have e2 := L_meta_53217.fiber_sum color (fun z => Disjoint z (L_meta_53217.cp color j)) w
    have e12 := e1.symm.trans e2
    refine (Eq.trans rfl e12).trans ?_
    show _ = k * (low j).sum M
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => hw z)
  have margK : ∀ w : W → ℕ, (∀ z, canonMass w z = k * M z) → ∀ f g,
      L_meta_53217.Loc color f → L_meta_53217.Loc color g → delta f = delta g →
      (Finset.univ.filter (fun x => f x ≠ g x)).sum w = k * dist M f g := by
    intro w hw f g hf hg hd
    have e2 := L_meta_53217.fiber_sum color (fun z => f z ≠ g z) w
    refine (Finset.sum_congr ?_ (fun _ _ => rfl)).trans (e2.trans ?_)
    · ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact L_meta_53217.loc_norm color hne f g hf hg (fun j => congrFun hd j) x
    · dsimp only [dist]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun z _ => hw z)
  have pairDis : ∀ f g, L_meta_53217.Loc color f → L_meta_53217.Loc color g → ∀ j,
      delta f j ≠ delta g j → ∀ u, Disjoint u (comp j) →
        f u ≠ g u ∨ f (L_meta_53217.up u (comp j)) ≠ g (L_meta_53217.up u (comp j)) := by
    intro f g hf hg j hj u hu
    have s1 := L_meta_53217.loc_step color f hf u j hu
    have s2 := L_meta_53217.loc_step color g hg u j hu
    by_contra hc
    push Not at hc
    apply hj
    show ((f (comp j)).toNat : ℤ) - (f ∅).toNat = ((g (comp j)).toNat : ℤ) - (g ∅).toNat
    unfold L_meta_53217.up at hc
    rw [hcomp] at hc
    rw [hcomp, ← s1, ← s2, hc.1, hc.2]
  have dis : ∀ w : W → ℕ, ∀ f g, L_meta_53217.Loc color f → L_meta_53217.Loc color g → ∀ j,
      delta f j ≠ delta g j →
      (low j).sum (fun u => min (w u) (w (L_meta_53217.up u (comp j)))) ≤
        (Finset.univ.filter (fun x => f x ≠ g x)).sum w := by
    intro w f g hf hg j hj
    have e1 := L_meta_53217.pair_sum color j (hne j) (fun x => if f x ≠ g x then w x else 0)
    calc (low j).sum (fun u => min (w u) (w (L_meta_53217.up u (comp j))))
        ≤ (low j).sum (fun u => (if f u ≠ g u then w u else 0) +
            (if f (L_meta_53217.up u (comp j)) ≠ g (L_meta_53217.up u (comp j))
              then w (L_meta_53217.up u (comp j)) else 0)) := by
          apply Finset.sum_le_sum
          intro u hu
          have hu' : Disjoint u (comp j) := by simpa [low] using hu
          rcases pairDis f g hf hg j hj u hu' with h | h
          · simp only [h, ite_true, ne_eq, not_false_eq_true]
            exact (min_le_left _ _).trans (Nat.le_add_right _ _)
          · simp only [h, ne_eq, not_false_eq_true, ite_true]
            exact (min_le_right _ _).trans (Nat.le_add_left _ _)
      _ = _ := e1.symm
      _ ≤ Finset.univ.sum (fun x => if f x ≠ g x then w x else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.zero_le _)
      _ = _ := (Finset.sum_filter _ _).symm
  have minPair : ∀ a b' : ℕ, 2 * min a b' ≤ a + b' := by
    intro a b'; rcases le_total a b' with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  constructor
  · rintro ⟨w, hw, hv⟩
    rcases Nat.eq_zero_or_pos D with hD0 | hDpos
    · have hb0 : b = 0 := by
        rcases Nat.eq_zero_or_pos b with h | h
        · exact h
        · exfalso; have := Nat.mul_pos hk h; omega
      subst hb0
      refine ⟨fun j => Nat.zero_le _, fun f g _ => Nat.zero_le _, ?_⟩
      intro z _
      by_cases hMz : M z = 0
      · rw [hMz, mul_zero]; exact dvd_zero _
      · rw [Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem ?_), pow_zero]
        · exact one_dvd _
        · intro j hj'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
          have hj := hj'
          have hzl : z ∈ low j := by simp [low, hj.1]
          have : M z ≤ neutral M j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hzl
          omega
    · obtain ⟨h1, h2, h3⟩ := (VAL D w hDpos).1 hv
      simp only [unionEq] at h1
      have pk := pairK w hw
      have twoMin : ∀ j, 2 * (low j).sum (fun u => min (w u) (w (L_meta_53217.up u (comp j)))) ≤
          k * neutral M j := by
        intro j
        rw [← pk j, Finset.mul_sum]
        exact Finset.sum_le_sum (fun u _ => minPair _ _)
      refine ⟨?_, ?_, ?_⟩
      · intro j
        have := h1 j
        have := twoMin j
        exact Nat.le_of_mul_le_mul_left (by omega) hk
      · rintro f g ⟨hf, hg', hd⟩
        have hlg : L_meta_53217.Loc color g := by
          rcases hg' with hg | ⟨hg, _⟩
          · exact locR g hg
          · exact locN g hg
        have mk := margK w hw f g (locN f hf) hlg hd
        have hm : D ≤ (Finset.univ.filter (fun x => f x ≠ g x)).sum w := by
          rcases hg' with hg | ⟨hg, hfg⟩
          · exact h3 f hf g hg
          · exact h2 f hf g hg hfg
        rw [mk] at hm
        have : k * b ≤ k * (2 * dist M f g) := by
          have e : k * (2 * dist M f g) = 2 * (k * dist M f g) := by ring
          omega
        exact Nat.le_of_mul_le_mul_left this hk
      · intro z _
        rw [← hw z]
        dsimp only [canonMass]
        refine ⟨_, L_meta_53217.halve color hne z w _ ?_ ?_⟩
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact hj.1
        · intro j hj u hu hd
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have hsum : (low j).sum (fun u => 2 * min (w u) (w (L_meta_53217.up u (comp j)))) =
              (low j).sum (fun u => w u + w (L_meta_53217.up u (comp j))) := by
            apply le_antisymm (Finset.sum_le_sum (fun u _ => minPair _ _))
            rw [← Finset.mul_sum, pk j, hj.2]
            have := h1 j
            omega
          have hu' : u ∈ low j := by
            simp only [low, Finset.mem_filter, Finset.mem_univ, true_and]; exact hd
          have := (Finset.sum_eq_sum_iff_of_le (fun u _ => minPair _ _)).1 hsum u hu'
          have h4 : w u = w (L_meta_53217.up u (comp j)) := by
            rcases le_total (w u) (w (L_meta_53217.up u (comp j))) with h | h
            · rw [min_eq_left h] at this; omega
            · rw [min_eq_right h] at this; omega
          exact h4.symm
  · rintro ⟨ha, hb, hc⟩
    let Tt : W → Finset (Fin c) := fun z =>
      Finset.univ.filter (fun j : Fin c => Disjoint z (comp j) ∧ neutral M j = b)
    have memTt : ∀ z j, j ∈ Tt z ↔ Disjoint z (comp j) ∧ neutral M j = b := by
      intro z j; simp [Tt]
    have hTt : ∀ z, norm z = z → 2 ^ (Tt z).card ∣ k * M z := by
      intro z hz
      have := hc z hz
      convert this using 3
      ext j; simp [Tt]
    let base : W → Finset W := fun z =>
      Finset.univ.filter (fun y => norm y = z ∧ ∀ j ∈ Tt z, Disjoint y (comp j))
    let m : W → ℕ := fun z => k * M z / 2 ^ (Tt z).card
    let N : W → ℕ := fun z => (base z).card
    have exR : ∀ z, ∃ R ⊆ base z, R.card = min (m z % N z) (N z) :=
      fun z => Finset.exists_subset_card_eq (min_le_right _ _)
    choose R hRsub hRcard using exR
    let strip : W → W → W := fun z x => x.filter (fun i => color i ∉ Tt z)
    let w : W → ℕ := fun x =>
      m (norm x) / N (norm x) + if strip (norm x) x ∈ R (norm x) then 1 else 0
    have stripU : ∀ z j u, j ∈ Tt z → Disjoint u (comp j) →
        strip z (L_meta_53217.up u (comp j)) = strip z u := by
      intro z j u hj hd
      ext i
      simp only [strip, L_meta_53217.up, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact ⟨h1, h2⟩
        · exfalso; apply h2
          have : color i = j := (L_meta_53217.mem_cp _ _ _).1 h1
          rw [this]; exact hj
      · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
    have normU : ∀ j u, Disjoint u (comp j) → norm (L_meta_53217.up u (comp j)) = norm u :=
      fun j u hd => L_meta_53217.nm_union color u j hd
    have wU : ∀ j u, Disjoint u (comp j) → j ∈ Tt (norm u) →
        w (L_meta_53217.up u (comp j)) = w u := by
      intro j u hd hj
      simp only [w]
      rw [normU j u hd, stripU _ j u hj hd]
    have hwc : ∀ z, canonMass w z = k * M z := by
      intro z
      by_cases hz : norm z = z
      · have hal := L_meta_53217.halve color hne z w (Tt z)
          (fun j hj => ((memTt z j).1 hj).1)
          (fun j hj u hu hd => by
            have := wU j u hd (by rw [show norm u = z from hu]; exact hj)
            exact this)
        dsimp only [canonMass]
        refine hal.trans ?_
        have hb' : (base z).sum w = m z := by
          have ebase : ∀ x ∈ base z, w x = m z / N z + if x ∈ R z then 1 else 0 := by
            intro x hx
            simp only [base, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            have hs : strip z x = x := by
              ext i
              simp only [strip, Finset.mem_filter, and_iff_left_iff_imp]
              intro hi hci
              exact Finset.disjoint_left.1 (hx.2 _ hci) hi ((L_meta_53217.mem_cp _ _ _).2 rfl)
            simp only [w, hx.1, hs]
          have hzb : z ∈ base z := by
            simp only [base, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hz, fun j hj => ((memTt z j).1 hj).1⟩
          have hN : 0 < N z := Finset.card_pos.2 ⟨z, hzb⟩
          calc (base z).sum w = (base z).sum (fun x => m z / N z + if x ∈ R z then 1 else 0) :=
                Finset.sum_congr rfl ebase
            _ = N z * (m z / N z) + (R z).card := by
                rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole,
                  Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hRsub z)]
                rfl
            _ = m z := by
                rw [hRcard z, min_eq_left (Nat.mod_lt _ hN).le]
                exact Nat.div_add_mod _ _
        calc 2 ^ (Tt z).card * _ = 2 ^ (Tt z).card * (base z).sum w := by
              congr 1
              apply Finset.sum_congr _ (fun _ _ => rfl)
              ext x
              simp only [base, Finset.mem_filter, Finset.mem_univ, true_and]
              rfl
          _ = 2 ^ (Tt z).card * m z := by rw [hb']
          _ = k * M z := Nat.mul_div_cancel' (hTt z hz)
      · have : M z = 0 := hM z hz
        rw [this, mul_zero]
        dsimp only [canonMass]
        apply Finset.sum_eq_zero
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exfalso; apply hz; rw [← hx]; exact L_meta_53217.nm_nm color x
    refine ⟨w, hwc, ?_⟩
    rcases Nat.eq_zero_or_pos D with hD0 | hDpos
    · intro lost hl; omega
    have pk := pairK w hwc
    have one : ∀ j, D ≤ (low j).sum (fun u => min (w u) (w (L_meta_53217.up u (comp j)))) := by
      intro j
      rcases (ha j).lt_or_eq with hlt | heq
      ·
        have per : ∀ u ∈ low j, w u + w (L_meta_53217.up u (comp j)) ≤
            2 * min (w u) (w (L_meta_53217.up u (comp j))) +
              (if 0 < M (norm u) then 1 else 0) := by
          intro u hu
          have hd : Disjoint u (comp j) := by
            simp only [low, Finset.mem_filter, Finset.mem_univ, true_and] at hu; exact hu
          simp only [w]
          rw [normU j u hd]
          by_cases hM0 : 0 < M (norm u)
          · simp only [hM0, ite_true]
            split_ifs <;> omega
          · have hm0 : m (norm u) = 0 := by
              simp only [m]; rw [show M (norm u) = 0 by omega]; simp
            have hR0 : R (norm u) = ∅ := by
              apply Finset.card_eq_zero.1
              rw [hRcard, hm0]; simp
            simp [hm0, hR0, hM0]
        have hcount : (low j).sum (fun u => if 0 < M (norm u) then 1 else 0) ≤
            k * (neutral M j - b) := by
          rw [Finset.sum_boole]
          rcases hslack with hs | hs
          · have h1 : ((low j).filter (fun u => 0 < M (norm u))).card ≤ 2 ^ n := by
              calc _ ≤ (Finset.univ : Finset W).card := Finset.card_le_univ _
                _ = 2 ^ n := by simp [W]
            have h2 : k ≤ k * (neutral M j - b) := Nat.le_mul_of_pos_right _ (by omega)
            simp only [Nat.cast_id]
            omega
          · have := hs j hlt
            simp only [Nat.cast_id]
            convert this using 2
            ext x; simp
        have tot : (low j).sum (fun u => w u + w (L_meta_53217.up u (comp j))) ≤
            2 * (low j).sum (fun u => min (w u) (w (L_meta_53217.up u (comp j)))) +
              (low j).sum (fun u => if 0 < M (norm u) then 1 else 0) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum per
        rw [pk j] at tot
        have hid : k * neutral M j = k * b + k * (neutral M j - b) := by
          rw [← mul_add, Nat.add_sub_cancel' hlt.le]
        omega
      ·
        have eqs : ∀ u ∈ low j, w (L_meta_53217.up u (comp j)) = w u := by
          intro u hu
          have hd : Disjoint u (comp j) := by
            simp only [low, Finset.mem_filter, Finset.mem_univ, true_and] at hu; exact hu
          apply wU j u hd
          rw [memTt]
          exact ⟨Finset.disjoint_of_subset_left (L_meta_53217.nm_sub _ _) hd, heq.symm⟩
        have : 2 * (low j).sum (fun u => min (w u) (w (L_meta_53217.up u (comp j)))) =
            k * neutral M j := by
          rw [← pk j, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          rw [eqs u hu, min_self]; ring
        rw [← heq] at this
        omega
    have gap : ∀ f g, L_meta_53217.Loc color f → L_meta_53217.Loc color g →
        (delta f = delta g → b ≤ 2 * dist M f g) →
        D ≤ (Finset.univ.filter (fun x => f x ≠ g x)).sum w := by
      intro f g hf hg hcmp
      by_cases hd : delta f = delta g
      · rw [margK w hwc f g hf hg hd]
        have := hcmp hd
        have : k * b ≤ k * (2 * dist M f g) := Nat.mul_le_mul_left k this
        have e : k * (2 * dist M f g) = 2 * (k * dist M f g) := by ring
        omega
      · obtain ⟨j, hj⟩ : ∃ j, delta f j ≠ delta g j := by
          by_contra h
          push Not at h
          exact hd (funext h)
        exact (one j).trans (dis w f g hf hg j hj)
    refine (VAL D w hDpos).2 ⟨?_, ?_, ?_⟩
    · intro j; rw [show (fun u => min (w u) (w (u ∪ comp j))) =
        (fun u => min (w u) (w (L_meta_53217.up u (comp j)))) from by simp only [unionEq]]
      exact one j
    · intro f hf g hg hfg
      exact gap f g (locN f hf) (locN g hg) (fun hd => hb f g ⟨hf, Or.inr ⟨hg, hfg⟩, hd⟩)
    · intro f hf g hg
      exact gap f g (locN f hf) (locR g hg) (fun hd => hb f g ⟨hf, Or.inl hg, hd⟩)
