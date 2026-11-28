import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1526_aux

open Finset

def gain {n : ℕ} (v : Finset (Fin n) → ℕ) (i : Fin n) : ℕ :=
  ∑ A ∈ (univ.filter (fun A : Finset (Fin n) => i ∉ A)), min (v A) (v (insert i A))

theorem gain_out {n : ℕ} (v : Finset (Fin n) → ℕ) (S : Finset (Fin n))
    (hv : ∀ A, ¬ A ⊆ S → v A = 0) (i : Fin n) (hi : i ∉ S) : gain v i = 0 := by
  unfold gain
  apply sum_eq_zero
  intro A _
  rw [hv (insert i A) (fun h => hi (h (mem_insert_self i A)))]
  simp

theorem gain_ins {n : ℕ} (v : Finset (Fin n) → ℕ) (x : Fin n) (R : Finset (Fin n)) (hx : x ∉ R)
    (hv : ∀ A, ¬ A ⊆ insert x R → v A = 0) :
    gain v x = ∑ t ∈ R.powerset, min (v t) (v (insert x t)) := by
  unfold gain
  symm
  apply sum_subset
  · intro t ht
    simp only [mem_powerset] at ht
    simp only [mem_filter, mem_univ, true_and]
    exact fun h => hx (ht h)
  · intro A hA hA'
    simp only [mem_filter, mem_univ, true_and] at hA
    simp only [mem_powerset] at hA'
    rw [hv A (fun h => hA' ((subset_insert_iff_of_notMem hA).1 h))]
    simp

theorem sum_ins {n : ℕ} (v : Finset (Fin n) → ℕ) (x : Fin n) (R : Finset (Fin n)) (hx : x ∉ R)
    (hv : ∀ A, ¬ A ⊆ insert x R → v A = 0) :
    ∑ A, v A = ∑ t ∈ R.powerset, (v t + v (insert x t)) := by
  rw [sum_add_distrib, ← sum_powerset_insert hx]
  symm
  apply sum_subset (subset_univ _)
  intro A _ hA
  exact hv A (fun h => hA (mem_powerset.2 h))

theorem ps1 {n : ℕ} (b : Fin n) : ({b} : Finset (Fin n)).powerset = {∅, {b}} := by
  ext t; simp [subset_singleton_iff]

theorem two {n : ℕ} (v : Finset (Fin n) → ℕ) (a b : Fin n) (hab : a ≠ b)
    (hv : ∀ A, ¬ A ⊆ {a, b} → v A = 0) :
    ∑ A, v A = v ∅ + v {a} + v {b} + v {a, b} ∧
    gain v a = min (v ∅) (v {a}) + min (v {b}) (v {a, b}) ∧
    gain v b = min (v ∅) (v {b}) + min (v {a}) (v {a, b}) := by
  have ha : a ∉ ({b} : Finset (Fin n)) := by simpa using hab
  have hb : b ∉ ({a} : Finset (Fin n)) := by simpa using hab.symm
  have hv2 : ∀ A, ¬ A ⊆ insert b {a} → v A = 0 := by
    intro A h; exact hv A (by rwa [pair_comm])
  have s := sum_ins v a {b} ha hv
  have ga := gain_ins v a {b} ha hv
  have gb := gain_ins v b {a} hb hv2
  rw [ps1, sum_pair (singleton_ne_empty _).symm] at s ga gb
  refine ⟨?_, ?_, ?_⟩
  · rw [s]; simp; omega
  · rw [ga]; simp
  · rw [gb]; simp [pair_comm b a]

theorem one {n : ℕ} (v : Finset (Fin n) → ℕ) (a : Fin n)
    (hv : ∀ A, ¬ A ⊆ {a} → v A = 0) :
    ∑ A, v A = v ∅ + v {a} ∧ gain v a = min (v ∅) (v {a}) := by
  have hv' : ∀ A, ¬ A ⊆ insert a ∅ → v A = 0 := by simpa using hv
  have s := sum_ins v a ∅ (notMem_empty a) hv'
  have g := gain_ins v a ∅ (notMem_empty a) hv'
  simp at s g
  exact ⟨s, g⟩

theorem upper {n : ℕ} (v : Finset (Fin n) → ℕ) (S : Finset (Fin n)) (m : ℕ) (c : Prop) [Decidable c]
    (hc : c ↔ S.card = 2 ∧ m % 4 = 2) (hS : S.card ≤ 2)
    (hv : ∀ A, ¬ A ⊆ S → v A = 0) (hm : ∑ A, v A = m) :
    ∑ i ∈ S, (gain v i - (m / 2 - (if c then 1 else 0))) ≤ (if c then 1 else 0) := by
  obtain h0 | h1 | h2 : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  · rw [card_eq_zero] at h0; subst h0; simp
  · obtain ⟨a, rfl⟩ := card_eq_one.1 h1
    obtain ⟨s, g⟩ := one v a hv
    have : ¬ c := by rw [hc]; simp
    simp [g, this]; omega
  · obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 h2
    obtain ⟨s, ga, gb⟩ := two v a b hab hv
    rw [sum_pair hab, ga, gb]
    have hcc : c ↔ m % 4 = 2 := by rw [hc, h2]; simp
    by_cases hm4 : m % 4 = 2
    · rw [if_pos (hcc.2 hm4)]; omega
    · rw [if_neg (fun h => hm4 (hcc.1 h))]; omega

theorem build {n : ℕ} (S : Finset (Fin n)) (m : ℕ) (c : Prop) [Decidable c]
    (hc : c ↔ S.card = 2 ∧ m % 4 = 2) (hS : S.card ≤ 2)
    (P : Fin n → Prop) [DecidablePred P] (hP : ∀ i, P i → c ∧ i ∈ S)
    (hP1 : ∀ i j, P i → P j → i = j) :
    ∃ v : Finset (Fin n) → ℕ, (∑ A, v A = m) ∧ (∀ A, ¬ A ⊆ S → v A = 0) ∧
      ∀ i, (if i ∈ S then m / 2 - (if c then 1 else 0) else 0) + (if P i then 1 else 0) ≤ gain v i := by
  obtain h0 | h1 | h2 : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  · rw [card_eq_zero] at h0; subst h0
    refine ⟨fun A => if A = ∅ then m else 0, by simp, ?_, ?_⟩
    · intro A hA; simp only [ite_eq_right_iff]; rintro rfl; exact absurd (empty_subset _) hA
    · intro i
      have : ¬ P i := fun h => by simpa using (hP i h).2
      simp [this]
  · obtain ⟨a, rfl⟩ := card_eq_one.1 h1
    have nc : ¬ c := by rw [hc]; simp
    let v : Finset (Fin n) → ℕ := fun A => if A ⊆ {a} then (if a ∈ A then m / 2 else m - m / 2) else 0
    have hv : ∀ A, ¬ A ⊆ {a} → v A = 0 := fun A hA => if_neg hA
    obtain ⟨s, g⟩ := one v a hv
    refine ⟨v, ?_, hv, ?_⟩
    · rw [s]; simp [v]; omega
    · intro i
      have : ¬ P i := fun h => nc (hP i h).1
      by_cases hi : i = a
      · subst hi; rw [g]; simp [v, this, nc]; omega
      · simp [hi, this]
  · obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 h2
    have hcc : c ↔ m % 4 = 2 := by rw [hc, h2]; simp
    let v : Finset (Fin n) → ℕ := fun A => if A ⊆ {a, b} then
      (if a ∈ A then (if b ∈ A then m / 4 + (if m % 4 = 1 ∨ m % 4 = 3 then 1 else 0)
        else m / 4 + (if m % 4 = 3 ∨ (m % 4 = 2 ∧ P a) then 1 else 0))
      else (if b ∈ A then m / 4 + (if m % 4 = 3 ∨ (m % 4 = 2 ∧ ¬ P a) then 1 else 0)
        else m / 4 + (if m % 4 = 2 then 1 else 0))) else 0
    have hv : ∀ A, ¬ A ⊆ {a, b} → v A = 0 := fun A hA => if_neg hA
    obtain ⟨hs, ga, gb⟩ := two v a b hab hv
    have e0 : v ∅ = m / 4 + (if m % 4 = 2 then 1 else 0) := by simp [v]
    have e1 : v {a} = m / 4 + (if m % 4 = 3 ∨ (m % 4 = 2 ∧ P a) then 1 else 0) := by
      simp [v, Ne.symm hab]
    have e2 : v {b} = m / 4 + (if m % 4 = 3 ∨ (m % 4 = 2 ∧ ¬ P a) then 1 else 0) := by
      simp [v, hab]
    have e3 : v {a, b} = m / 4 + (if m % 4 = 1 ∨ m % 4 = 3 then 1 else 0) := by simp [v]
    refine ⟨v, ?_, hv, ?_⟩
    · rw [hs, e0, e1, e2, e3]
      have h4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
      rcases h4 with h4 | h4 | h4 | h4 <;> by_cases hpa : P a <;> simp [h4, hpa] <;> omega
    · intro i
      by_cases hi : i ∈ ({a, b} : Finset (Fin n))
      · rw [if_pos hi]
        have h4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
        rcases mem_insert.1 hi with rfl | hi'
        · rw [ga, e0, e1, e2, e3]
          by_cases hpa : P i
          · have hc' := (hP i hpa).1
            have := hcc.1 hc'
            simp [hc', hpa, this]; omega
          · rcases h4 with h4 | h4 | h4 | h4 <;> simp [hcc, hpa, h4] <;> omega
        · rw [mem_singleton] at hi'; subst hi'
          rw [gb, e0, e1, e2, e3]
          by_cases hpb : P i
          · have hc' := (hP i hpb).1
            have hpa : ¬ P a := fun h' => hab (hP1 _ _ h' hpb)
            have := hcc.1 hc'
            simp [hc', hpb, hpa, this]; omega
          · rcases h4 with h4 | h4 | h4 | h4 <;> by_cases hpa : P a <;> simp [hcc, hpb, hpa, h4] <;> omega
      · have : ¬ P i := fun h => hi (hP i h).2
        simp [hi, this]

end PEqualNP.Outside.L_lib_1526_aux

open PEqualNP.Outside.L_lib_1526_aux Finset in
theorem PEqualNP.Outside.L_lib_1526 :
∀ (n f : Nat) (axes : Fin f → Finset (Fin n)) (mass : Fin f → Nat)
    (quota : Fin n → Nat), (∀ h, (axes h).card ≤ 2) →
  let W := Finset (Fin n)
  let contested := (Finset.univ : Finset (Fin f)).filter
    (fun h => (axes h).card = 2 ∧ mass h % 4 = 2)
  let base := fun i : Fin n => ∑ h : Fin f,
    if i ∈ axes h then mass h / 2 - (if h ∈ contested then 1 else 0) else 0
  (∃ w : Fin f → W → Nat,
    (∀ h, (∑ A, w h A) = mass h) ∧
    (∀ h A, ¬ A ⊆ axes h → w h A = 0) ∧
    ∀ i : Fin n, quota i ≤ ∑ h : Fin f,
      ∑ A ∈ (Finset.univ.filter (fun A : W => i ∉ A)),
        min (w h A) (w h (insert i A))) ↔
  ∀ T : Finset (Fin n), (∑ i ∈ T, (quota i - base i)) ≤
    (contested.filter (fun h => (axes h ∩ T).Nonempty)).card := by
  intro n f axes mass quota hax W contested base
  have hc : ∀ h, h ∈ contested ↔ (axes h).card = 2 ∧ mass h % 4 = 2 := by intro h; simp [contested]
  constructor
  · rintro ⟨w, hw1, hw2, hw3⟩ T
    have key : ∀ i, quota i - base i ≤ ∑ h, (gain (w h) i -
        (if i ∈ axes h then mass h / 2 - (if h ∈ contested then 1 else 0) else 0)) := by
      intro i
      have h3 : quota i ≤ ∑ h, gain (w h) i := hw3 i
      have e := sum_le_sum (fun h (_ : h ∈ (univ : Finset (Fin f))) =>
        show gain (w h) i ≤ (gain (w h) i - (if i ∈ axes h then mass h / 2 -
          (if h ∈ contested then 1 else 0) else 0)) +
          (if i ∈ axes h then mass h / 2 - (if h ∈ contested then 1 else 0) else 0) by omega)
      rw [sum_add_distrib] at e
      have hb : base i = ∑ h, (if i ∈ axes h then mass h / 2 - (if h ∈ contested then 1 else 0) else 0) := rfl
      omega
    calc ∑ i ∈ T, (quota i - base i)
        ≤ ∑ i ∈ T, ∑ h, (gain (w h) i -
          (if i ∈ axes h then mass h / 2 - (if h ∈ contested then 1 else 0) else 0)) :=
          sum_le_sum (fun i _ => key i)
      _ = ∑ h, ∑ i ∈ T, (gain (w h) i -
          (if i ∈ axes h then mass h / 2 - (if h ∈ contested then 1 else 0) else 0)) := sum_comm
      _ ≤ ∑ h, (if h ∈ contested ∧ (axes h ∩ T).Nonempty then 1 else 0) := by
          apply sum_le_sum
          intro h _
          rw [← sum_subset (inter_subset_right (s₁ := axes h))]
          · by_cases hne : (axes h ∩ T).Nonempty
            · refine (sum_le_sum_of_subset inter_subset_left).trans ?_
              have := upper (w h) (axes h) (mass h) (h ∈ contested) (hc h) (hax h) (hw2 h) (hw1 h)
              rw [sum_congr rfl (fun i hi => by rw [if_pos hi])]
              refine this.trans ?_
              by_cases hh : h ∈ contested <;> simp [hh, hne]
            · rw [not_nonempty_iff_eq_empty.1 hne]; simp
          · intro i hiT hi
            have hi' : i ∉ axes h := fun h' => hi (mem_inter.2 ⟨h', hiT⟩)
            simp [gain_out (w h) (axes h) (hw2 h) i hi', hi']
      _ = _ := by
          simp only [contested, card_filter, sum_filter, ite_and, mem_filter, mem_univ, true_and]
  · intro hT
    classical
    let ι := {p : Fin n × ℕ // p.2 < quota p.1 - base p.1}
    let t : ι → Finset (Fin f) := fun u => contested.filter (fun h => u.1.1 ∈ axes h)
    have hall : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card := by
      intro s
      have h1 : s.card ≤ ∑ i ∈ s.image (fun u => u.1.1), (quota i - base i) := by
        rw [card_eq_sum_card_image (fun u : ι => u.1.1) s]
        apply sum_le_sum
        intro i _
        have := card_le_card_of_injOn (fun u : ι => u.1.2) (s := s.filter (fun u => u.1.1 = i))
          (t := range (quota i - base i))
          (by intro u hu
              simp only [coe_filter, Set.mem_setOf_eq] at hu
              simp only [coe_range, Set.mem_Iio]; rw [← hu.2]; exact u.2)
          (by intro u hu u' hu' e
              simp only [coe_filter, Set.mem_setOf_eq] at hu hu'
              exact Subtype.ext (Prod.ext (hu.2.trans hu'.2.symm) e))
        simpa using this
      have h2 : contested.filter (fun h => (axes h ∩ s.image (fun u => u.1.1)).Nonempty) ⊆
          s.biUnion t := by
        intro h hh
        simp only [mem_filter] at hh
        obtain ⟨i, hi⟩ := hh.2
        simp only [mem_inter, mem_image] at hi
        obtain ⟨hia, u, hu, rfl⟩ := hi
        exact mem_biUnion.2 ⟨u, hu, mem_filter.2 ⟨hh.1, hia⟩⟩
      exact h1.trans ((hT _).trans (card_le_card h2))
    obtain ⟨g, ginj, gmem⟩ := (all_card_le_biUnion_card_iff_exists_injective t).1 hall
    let sel : Fin f → Fin n → Prop := fun h i => ∃ u : ι, g u = h ∧ u.1.1 = i
    have loc : ∀ h, ∃ v : Finset (Fin n) → ℕ, (∑ A, v A = mass h) ∧ (∀ A, ¬ A ⊆ axes h → v A = 0) ∧
        ∀ i, (if i ∈ axes h then mass h / 2 - (if h ∈ contested then 1 else 0) else 0) +
          (if sel h i then 1 else 0) ≤ gain v i := by
      intro h
      refine build (axes h) (mass h) (h ∈ contested) (hc h) (hax h) (sel h) ?_ ?_
      · rintro i ⟨u, rfl, rfl⟩
        have := gmem u
        simp only [t, mem_filter] at this
        exact this
      · rintro i j ⟨u, rfl, rfl⟩ ⟨u', hu', rfl⟩
        rw [ginj hu']
    choose w hw1 hw2 hw3 using loc
    refine ⟨w, hw1, hw2, fun i => ?_⟩
    have cnt : quota i - base i ≤ (univ.filter (fun h => sel h i)).card := by
      have := card_le_card_of_injOn (fun j : Fin (quota i - base i) => g ⟨(i, j.1), j.2⟩)
        (s := univ) (t := univ.filter (fun h => sel h i))
        (by intro j _
            simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
            exact ⟨_, rfl, rfl⟩)
        (by intro j _ j' _ e
            have := congrArg (fun u : ι => u.1.2) (ginj e)
            exact Fin.ext this)
      simpa using this
    rw [card_filter] at cnt
    have e := sum_le_sum (fun h (_ : h ∈ (univ : Finset (Fin f))) => hw3 h i)
    rw [sum_add_distrib] at e
    have hb : base i = ∑ h, (if i ∈ axes h then mass h / 2 - (if h ∈ contested then 1 else 0) else 0) := rfl
    show quota i ≤ ∑ h, gain (w h) i
    omega
