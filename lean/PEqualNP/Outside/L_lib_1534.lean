import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1534

private abbrev W := Finset (Fin 3)

private def ov (u : W → Nat) (j : Fin 3) : Nat :=
  ∑ A ∈ (Finset.univ.filter (fun A : W => j ∉ A)), min (u A) (u (insert j A))

private theorem total (u : W → Nat) :
    (∑ A, u A) =
      u ∅ + u {0} + u {1} + u {0, 1} + u {2} + u {0, 2} + u {1, 2} + u {0, 1, 2} := by
  have h : (Finset.univ : Finset W) =
      {∅, {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide +kernel
  rw [h]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  ac_rfl

private theorem ov_zero (u : W → Nat) :
    ov u 0 = min (u ∅) (u {0}) + min (u {1}) (u {0, 1}) +
      min (u {2}) (u {0, 2}) + min (u {1, 2}) (u {0, 1, 2}) := by
  have h : (Finset.univ.filter (fun A : W => 0 ∉ A)) =
      {∅, {1}, {2}, {1, 2}} := by decide +kernel
  unfold ov
  rw [h]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton, Finset.insert_empty]
  ac_rfl

private theorem ov_one (u : W → Nat) :
    ov u 1 = min (u ∅) (u {1}) + min (u {0}) (u {0, 1}) +
      min (u {2}) (u {1, 2}) + min (u {0, 2}) (u {0, 1, 2}) := by
  have h : (Finset.univ.filter (fun A : W => 1 ∉ A)) =
      {∅, {0}, {2}, {0, 2}} := by decide +kernel
  have h₁ : insert (1 : Fin 3) ({0} : W) = {0, 1} := by decide +kernel
  have h₂ : insert (1 : Fin 3) ({0, 2} : W) = {0, 1, 2} := by decide +kernel
  unfold ov
  rw [h]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton, Finset.insert_empty, h₁, h₂]
  ac_rfl

private theorem ov_two (u : W → Nat) :
    ov u 2 = min (u ∅) (u {2}) + min (u {0}) (u {0, 2}) +
      min (u {1}) (u {1, 2}) + min (u {0, 1}) (u {0, 1, 2}) := by
  have h : (Finset.univ.filter (fun A : W => 2 ∉ A)) =
      {∅, {0}, {1}, {0, 1}} := by decide +kernel
  have h₁ : insert (2 : Fin 3) ({0} : W) = {0, 2} := by decide +kernel
  have h₂ : insert (2 : Fin 3) ({1} : W) = {1, 2} := by decide +kernel
  have h₃ : insert (2 : Fin 3) ({0, 1} : W) = {0, 1, 2} := by decide +kernel
  unfold ov
  rw [h]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton, Finset.insert_empty, h₁, h₂, h₃]
  ac_rfl

private theorem paired (a b c d e f g h : Nat)
    (ht : a + b + c + d + e + f + g + h = 4) :
    let m := min a b + min c d + min e f + min g h
    m ≤ 2 ∧ (m = 2 → a = b ∧ c = d ∧ e = f ∧ g = h) := by
  dsimp
  have hab₁ := min_le_left a b
  have hab₂ := min_le_right a b
  have hcd₁ := min_le_left c d
  have hcd₂ := min_le_right c d
  have hef₁ := min_le_left e f
  have hef₂ := min_le_right e f
  have hgh₁ := min_le_left g h
  have hgh₂ := min_le_right g h
  exact ⟨by omega, fun hm => ⟨by omega, by omega, by omega, by omega⟩⟩

private theorem cube (u : W → Nat) (ht : (∑ A, u A) = 4) :
    (∀ j, ov u j ≤ 2) ∧
    (0 < ov u 0 → 0 < ov u 1 → 0 < ov u 2 → ov u 1 = 1 ∧ ov u 2 = 1) := by
  rw [total] at ht
  let a := u ∅
  let b := u {0}
  let c := u {1}
  let d := u {0, 1}
  let e := u {2}
  let f := u {0, 2}
  let g := u {1, 2}
  let h := u {0, 1, 2}
  change a + b + c + d + e + f + g + h = 4 at ht
  have hx := paired a b c d e f g h ht
  have hy := paired a c b d e g f h (by omega)
  have hz := paired a e b f c g d h (by omega)
  dsimp only at hx hy hz
  refine ⟨?_, ?_⟩
  · intro j
    fin_cases j
    · exact (ov_zero u).trans_le hx.1
    · exact (ov_one u).trans_le hy.1
    · exact (ov_two u).trans_le hz.1
  · rw [ov_zero, ov_one, ov_two]
    let x := min a b + min c d + min e f + min g h
    let y := min a c + min b d + min e g + min f h
    let z := min a e + min b f + min c g + min d h
    change 0 < x → 0 < y → 0 < z → y = 1 ∧ z = 1
    intro xp yp zp
    have xb : x ≤ 2 := hx.1
    have yb : y ≤ 2 := hy.1
    have zb : z ≤ 2 := hz.1
    have impossible (hx₂ : x = 2) (hy₂ : y = 2) (hz₂ : z = 2) : False := by
      obtain ⟨hab, hcd, hef, hgh⟩ := hx.2 hx₂
      obtain ⟨hac, _, heg, _⟩ := hy.2 hy₂
      obtain ⟨hae, _, _, _⟩ := hz.2 hz₂
      omega
    have evenOfX (hx₂ : x = 2) : y = 2 ∧ z = 2 := by
      obtain ⟨hab, hcd, hef, hgh⟩ := hx.2 hx₂
      have ye : y = 2 * (min a c + min e g) := by
        dsimp only [y]
        rw [← hab, ← hcd, ← hef, ← hgh]
        omega
      have ze : z = 2 * (min a e + min c g) := by
        dsimp only [z]
        rw [← hab, ← hcd, ← hef, ← hgh]
        omega
      exact ⟨by omega, by omega⟩
    have yn : y ≠ 2 := by
      intro hy₂
      obtain ⟨hac, hbd, heg, hfh⟩ := hy.2 hy₂
      have xe : x = 2 * (min a b + min e f) := by
        dsimp only [x]
        rw [← hac, ← hbd, ← heg, ← hfh]
        omega
      have hx₂ : x = 2 := by omega
      exact impossible hx₂ hy₂ (evenOfX hx₂).2
    have zn : z ≠ 2 := by
      intro hz₂
      obtain ⟨hae, hbf, hcg, hdh⟩ := hz.2 hz₂
      have xe : x = 2 * (min a b + min c d) := by
        dsimp only [x]
        rw [← hae, ← hbf, ← hcg, ← hdh]
        omega
      have hx₂ : x = 2 := by omega
      exact impossible hx₂ (evenOfX hx₂).1 hz₂
    exact ⟨by omega, by omega⟩

private theorem balance {α : Type*} (s : Finset α) (f : α → Nat)
    (hb : ∀ t ∈ s, f t ≤ 2) :
    (∑ t ∈ s, f t) + (∑ t ∈ s, (2 - f t)) = 2 * s.card := by
  rw [← Finset.sum_add_distrib]
  calc
    (∑ t ∈ s, (f t + (2 - f t))) = ∑ _t ∈ s, 2 :=
      Finset.sum_congr rfl fun t ht => by have := hb t ht; omega
    _ = 2 * s.card := by simp [Nat.mul_comm]

private theorem loss_budget {α : Type*} (s : Finset α) (f : α → Nat)
    (hb : ∀ t ∈ s, f t ≤ 2) (hl : 2 * s.card - 1 ≤ ∑ t ∈ s, f t) :
    (∑ t ∈ s, (2 - f t)) ≤ 1 := by
  have := balance s f hb
  omega

private theorem positive_of_budget {α : Type*} (s : Finset α) (f : α → Nat)
    (h : (∑ t ∈ s, (2 - f t)) ≤ 1) {t : α} (ht : t ∈ s) : 0 < f t := by
  have hle : 2 - f t ≤ ∑ r ∈ s, (2 - f r) :=
    Finset.single_le_sum (f := fun r => 2 - f r) (fun _ _ => Nat.zero_le _) ht
  omega

private theorem unique_loss {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Nat)
    (h : (∑ t ∈ s, (2 - f t)) ≤ 1) {t r : α} (ht : t ∈ s) (hr : r ∈ s)
    (htl : f t = 1) (hrl : f r = 1) : t = r := by
  by_contra hne
  have hs : ({t, r} : Finset α) ⊆ s := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact ht
    · exact hr
  have hle : (∑ q ∈ ({t, r} : Finset α), (2 - f q)) ≤ ∑ q ∈ s, (2 - f q) :=
    Finset.sum_le_sum_of_subset hs
  simp [Finset.sum_insert, hne, htl, hrl] at hle
  omega

private def star (A : W) : Nat := if A.card ≤ 1 then 1 else 0

private def square (A : W) : Nat := if (0 : Fin 3) ∉ A then 1 else 0

private theorem star_total : (∑ A, star A) = 4 := by decide +kernel
private theorem star_ov (j : Fin 3) : ov star j = 1 := by
  fin_cases j <;> decide +kernel

private theorem square_total : (∑ A, square A) = 4 := by decide +kernel
private theorem square_ov (j : Fin 3) (hj : j ≠ 0) : ov square j = 2 := by
  fin_cases j
  · exact (hj rfl).elim
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_lib_1534

theorem PEqualNP.Outside.L_lib_1534 : ∀ (n : Nat) (E : Finset (Fin n × Fin n × Fin n)) (S : Finset (Fin n)),
  let name := fun (j : Fin 3) (t : Fin n × Fin n × Fin n) =>
    if j = 0 then t.1 else if j = 1 then t.2.1 else t.2.2
  let inc := fun (j : Fin 3) (v : Fin n) => E.filter (fun t => name j t = v)
  let W := Finset (Fin 3)
  let overlap := fun (u : W → Nat) (j : Fin 3) =>
    ∑ A ∈ (Finset.univ.filter (fun A : W => j ∉ A)), min (u A) (u (insert j A))
  (∃ w : (Fin n × Fin n × Fin n) → W → Nat,
    (∀ t ∈ E, (∑ A, w t A) = 4) ∧
    (∀ a ∈ S, 1 ≤ (inc 0 a).sum (fun t => overlap (w t) 0)) ∧
    ∀ (j : Fin 3), j ≠ 0 → ∀ v : Fin n,
      2 * (inc j v).card - 1 ≤ (inc j v).sum (fun t => overlap (w t) j)) ↔
  ∃ M ⊆ E, M.image (name 0) = S ∧
    ∀ (j : Fin 3) (v : Fin n), (M.filter (fun t => name j t = v)).card ≤ 1 := by
  open PEqualNP.Outside.L_lib_1534 in
  intro n E S name inc W overlap
  change (∃ w : (Fin n × Fin n × Fin n) → W → Nat,
    (∀ t ∈ E, (∑ A, w t A) = 4) ∧
    (∀ a ∈ S, 1 ≤ ∑ t ∈ inc 0 a, ov (w t) 0) ∧
    ∀ (j : Fin 3), j ≠ 0 → ∀ v : Fin n,
      2 * (inc j v).card - 1 ≤ ∑ t ∈ inc j v, ov (w t) j) ↔ _
  constructor
  · rintro ⟨w, htotal, hhits, hinc⟩
    have hb j v : ∀ t ∈ inc j v, ov (w t) j ≤ 2 := by
      intro t ht
      exact (cube (w t) (htotal t (Finset.mem_filter.mp ht).1)).1 j
    have budget j (hj : j ≠ 0) v :=
      loss_budget (inc j v) (fun t => ov (w t) j) (hb j v) (hinc j hj v)
    have hits (a : {a // a ∈ S}) :
        ∃ t ∈ inc 0 a.val, 0 < ov (w t) 0 := by
      by_contra! hz
      have he : (∑ t ∈ inc 0 a.val, ov (w t) 0) = 0 :=
        Finset.sum_eq_zero fun t ht => Nat.eq_zero_of_le_zero (hz t ht)
      have := hhits a.val a.property
      omega
    let pick (a : {a // a ∈ S}) := Classical.choose (hits a)
    have pick_mem (a : {a // a ∈ S}) : pick a ∈ inc 0 a.val :=
      (Classical.choose_spec (hits a)).1
    have pick_name (a : {a // a ∈ S}) : name 0 (pick a) = a.val :=
      (Finset.mem_filter.mp (pick_mem a)).2
    have pick_loss (a : {a // a ∈ S}) (j : Fin 3) (hj : j ≠ 0) :
        ov (w (pick a)) j = 1 := by
      have he := (Finset.mem_filter.mp (pick_mem a)).1
      have hp (k : Fin 3) (hk : k ≠ 0) : 0 < ov (w (pick a)) k :=
        positive_of_budget (inc k (name k (pick a))) (fun t => ov (w t) k)
          (budget k hk _) (Finset.mem_filter.mpr ⟨he, rfl⟩)
      have h := (cube (w (pick a)) (htotal _ he)).2 (Classical.choose_spec (hits a)).2
        (hp 1 (by decide)) (hp 2 (by decide))
      fin_cases j
      · exact (hj rfl).elim
      · exact h.1
      · exact h.2
    let M := S.attach.image pick
    have m_sub : M ⊆ E := by
      intro t ht
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_filter.mp (pick_mem a)).1
    refine ⟨M, m_sub, ?_, ?_⟩
    · ext a
      constructor
      · intro ha
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ht
        exact (pick_name b).symm ▸ b.property
      · intro ha
        exact Finset.mem_image.mpr
          ⟨pick ⟨a, ha⟩, Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _, rfl⟩,
           pick_name ⟨a, ha⟩⟩
    · intro j v
      apply Finset.card_le_one.mpr
      intro t ht r hr
      obtain ⟨htM, htv⟩ := Finset.mem_filter.mp ht
      obtain ⟨hrM, hrv⟩ := Finset.mem_filter.mp hr
      by_cases hj : j = 0
      · subst j
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp htM
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hrM
        have hab : a = b := Subtype.ext ((pick_name a).symm.trans (htv.trans
          (hrv.symm.trans (pick_name b))))
        exact congrArg pick hab
      · have hl (s : Fin n × Fin n × Fin n) (hs : s ∈ M) : ov (w s) j = 1 := by
          obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs
          exact pick_loss a j hj
        exact unique_loss (inc j v) (fun s => ov (w s) j) (budget j hj v)
          (Finset.mem_filter.mpr ⟨m_sub htM, htv⟩) (Finset.mem_filter.mpr ⟨m_sub hrM, hrv⟩)
          (hl t htM) (hl r hrM)
  · rintro ⟨M, hsub, himage, hmatch⟩
    let w (t : Fin n × Fin n × Fin n) : W → Nat := if t ∈ M then star else square
    refine ⟨w, ?_, ?_, ?_⟩
    · intro t _
      by_cases ht : t ∈ M
      · simpa only [w, if_pos ht] using star_total
      · simpa only [w, if_neg ht] using square_total
    · intro a ha
      rw [← himage] at ha
      obtain ⟨t, ht, hta⟩ := Finset.mem_image.mp ha
      have hs : t ∈ inc 0 a := Finset.mem_filter.mpr ⟨hsub ht, hta⟩
      have hle : ov (w t) 0 ≤ ∑ r ∈ inc 0 a, ov (w r) 0 :=
        Finset.single_le_sum (f := fun r => ov (w r) 0) (fun _ _ => Nat.zero_le _) hs
      simpa only [w, if_pos ht, star_ov] using hle
    · intro j hj v
      have hb (t : Fin n × Fin n × Fin n) : ov (w t) j ≤ 2 := by
        by_cases ht : t ∈ M
        · simp [w, ht, star_ov]
        · simp [w, ht, square_ov j hj]
      have he : (∑ t ∈ inc j v, (2 - ov (w t) j)) =
          ((inc j v).filter (fun t => t ∈ M)).card := by
        calc
          (∑ t ∈ inc j v, (2 - ov (w t) j)) = ∑ t ∈ inc j v, if t ∈ M then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro t _
            by_cases ht : t ∈ M
            · simp [w, ht, star_ov]
            · simp [w, ht, square_ov j hj]
          _ = _ := by
            symm
            rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      have hs : (inc j v).filter (fun t => t ∈ M) =
          M.filter (fun t => name j t = v) := by
        ext t
        simp only [inc, Finset.mem_filter]
        exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩⟩
      have hl := balance (inc j v) (fun t => ov (w t) j) (fun t _ => hb t)
      rw [he, hs] at hl
      have hm := hmatch j v
      omega
