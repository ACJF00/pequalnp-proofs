import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_476

lemma exists_third (a b : Fin 3) : ∃ x : Fin 3, x ≠ a ∧ x ≠ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma no_fourth (x a b c : Fin 3) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c)
    (hx1 : x ≠ a) (hx2 : x ≠ b) (hx3 : x ≠ c) : False := by
  fin_cases x <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all

lemma card_pair (k : Nat) :
    Fintype.card {p : Fin k × Fin k // p.1 < p.2} = Nat.choose k 2 := by
  let e : {p : Fin k × Fin k // p.1 < p.2} ≃ {s : Finset (Fin k) // s.card = 2} :=
    { toFun := fun p => ⟨{p.1.1, p.1.2}, Finset.card_pair (ne_of_lt p.2)⟩
      invFun := fun s =>
        ⟨(s.1.min' (Finset.card_pos.mp (by omega)), s.1.max' (Finset.card_pos.mp (by omega))), by
          have hpos : s.1.Nonempty := Finset.card_pos.mp (by omega)
          have hne : s.1.min' hpos ≠ s.1.max' hpos := by
            intro heq
            have hsub : s.1 ⊆ {s.1.min' hpos} := by
              intro x hx
              rw [Finset.mem_singleton]
              have h1 : s.1.min' hpos ≤ x := Finset.min'_le _ _ hx
              have h2 : x ≤ s.1.max' hpos := Finset.le_max' _ _ hx
              rw [← heq] at h2
              exact le_antisymm h2 h1
            have hc := Finset.card_le_card hsub
            rw [Finset.card_singleton] at hc
            have hs2 := s.2
            omega
          exact lt_of_le_of_ne (Finset.min'_le _ _ (Finset.max'_mem _ hpos)) hne⟩
      left_inv := fun ⟨⟨a, b⟩, hab⟩ => by
        apply Subtype.ext
        ext1
        · dsimp only
          apply le_antisymm
          · exact Finset.min'_le _ a (by simp)
          · apply Finset.le_min'
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact le_rfl
            · exact le_of_lt hab
        · dsimp only
          apply le_antisymm
          · apply Finset.max'_le
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact le_of_lt hab
            · exact le_rfl
          · exact Finset.le_max' _ b (by simp)
      right_inv := fun ⟨s, hs⟩ => by
        apply Subtype.ext
        dsimp only
        have hpos : s.Nonempty := Finset.card_pos.mp (by omega)
        have hlt : s.min' hpos < s.max' hpos := by
          apply lt_of_le_of_ne (Finset.min'_le _ _ (Finset.max'_mem _ _))
          intro heq
          have hsub : s ⊆ {s.min' hpos} := by
            intro x hx
            rw [Finset.mem_singleton]
            have h1 := Finset.min'_le s x hx
            have h2 := Finset.le_max' s x hx
            rw [← heq] at h2
            exact le_antisymm h2 h1
          have hc := Finset.card_le_card hsub
          rw [hs, Finset.card_singleton] at hc
          omega
        have hsub : ({s.min' hpos, s.max' hpos} : Finset (Fin k)) ⊆ s := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.min'_mem s hpos
          · exact Finset.max'_mem s hpos
        exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair (ne_of_lt hlt), hs]) }
  rw [Fintype.card_congr e]
  have h1 : Fintype.card {s : Finset (Fin k) // s.card = 2} =
      (Finset.powersetCard 2 (Finset.univ : Finset (Fin k))).card := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr
      { toFun := fun s => ⟨s.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.2⟩⟩
        invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h1, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem main_proof : ∀ k : Nat,
  let Pair := {p : Fin k × Fin k // p.1 < p.2}
  let extendsToHost := fun (E : Pair → Bool) (c : Option (Fin k) → Fin 3) =>
    ∃ d : Pair → Fin 3, ∀ p, E p = true →
      d p ≠ c none ∧ d p ≠ c (some p.val.1) ∧ d p ≠ c (some p.val.2)
  let query := fun (E : Pair → Bool) (p : Pair) =>
    ∃ c : Option (Fin k) → Fin 3, extendsToHost E c ∧
      c none ≠ c (some p.val.1) ∧ c none ≠ c (some p.val.2) ∧
      c (some p.val.1) ≠ c (some p.val.2)
  (∀ (E : Pair → Bool) (u v : Option (Fin k)), u ≠ v →
    ∀ a b : Fin 3, ∃ c : Option (Fin k) → Fin 3,
      extendsToHost E c ∧ c u = a ∧ c v = b) ∧
  (∀ (E : Pair → Bool) (p : Pair), query E p ↔ E p = false) ∧
  (∀ (b : Nat) (summary : (Pair → Bool) → (Fin b → Bool))
    (answer : (Fin b → Bool) → Pair → Bool),
    (∀ E p, answer (summary E) p = true ↔ query E p) → Nat.choose k 2 ≤ b) := by
  intro k
  dsimp only
  have hpart1 : ∀ (E : {p : Fin k × Fin k // p.1 < p.2} → Bool) (u v : Option (Fin k)), u ≠ v →
      ∀ a b : Fin 3, ∃ c : Option (Fin k) → Fin 3,
        (∃ d : {p : Fin k × Fin k // p.1 < p.2} → Fin 3, ∀ p, E p = true →
          d p ≠ c none ∧ d p ≠ c (some p.val.1) ∧ d p ≠ c (some p.val.2)) ∧ c u = a ∧ c v = b := by
    intro E u v huv a b
    obtain ⟨x, hxa, hxb⟩ := exists_third a b
    let c : Option (Fin k) → Fin 3 := fun w => if w = u then a else if w = v then b else a
    refine ⟨c, ⟨fun _ => x, fun p _ => ?_⟩, ?_, ?_⟩
    · have hc : ∀ w, x ≠ c w := by
        intro w
        dsimp only [c]
        split_ifs <;> assumption
      exact ⟨hc none, hc (some p.val.1), hc (some p.val.2)⟩
    · simp [c]
    · simp [c, huv.symm]
  have hpart2 : ∀ (E : {p : Fin k × Fin k // p.1 < p.2} → Bool) (p : {p : Fin k × Fin k // p.1 < p.2}),
      (∃ c : Option (Fin k) → Fin 3,
        (∃ d : {p : Fin k × Fin k // p.1 < p.2} → Fin 3, ∀ q, E q = true →
          d q ≠ c none ∧ d q ≠ c (some q.val.1) ∧ d q ≠ c (some q.val.2)) ∧
        c none ≠ c (some p.val.1) ∧ c none ≠ c (some p.val.2) ∧
        c (some p.val.1) ≠ c (some p.val.2)) ↔ E p = false := by
    intro E p
    constructor
    · rintro ⟨c, ⟨d, hd⟩, h1, h2, h3⟩
      cases hep : E p with
      | false => rfl
      | true =>
        obtain ⟨hn, hp1, hp2⟩ := hd p hep
        exact (no_fourth (d p) (c none) (c (some p.val.1)) (c (some p.val.2)) h1 h2 h3 hn hp1 hp2).elim
    · intro hep
      let c : Option (Fin k) → Fin 3 := fun w =>
        if w = some p.val.1 then 1 else if w = some p.val.2 then 2 else 0
      let d : {q : Fin k × Fin k // q.1 < q.2} → Fin 3 := fun q =>
        if q.val.1 = p.val.1 ∨ q.val.2 = p.val.1 then 2 else 1
      have hp12 : p.val.1 ≠ p.val.2 := ne_of_lt p.2
      refine ⟨c, ⟨d, fun q hq => ?_⟩, ?_, ?_, ?_⟩
      · have hqp : q ≠ p := by
          intro heq
          subst heq
          rw [hep] at hq
          exact Bool.noConfusion hq
        have hne0 : d q ≠ c none := by
          dsimp only [d, c]
          simp only [reduceCtorEq, ↓reduceIte]
          split_ifs <;> decide
        refine ⟨hne0, ?_, ?_⟩
        · dsimp only [d, c]
          by_cases h1 : q.val.1 = p.val.1 ∨ q.val.2 = p.val.1
          · rw [if_pos h1]
            have hq1_ne_p2 : q.val.1 ≠ p.val.2 := by
              intro h
              rcases h1 with h1 | h1
              · exact hp12 (h1.symm.trans h)
              · have := lt_trans p.2 (h ▸ q.2)
                rw [h1] at this
                exact lt_irrefl _ this
            have hs : some q.val.1 ≠ some p.val.2 := fun h => hq1_ne_p2 (Option.some.inj h)
            rw [if_neg hs]
            split_ifs <;> decide
          · rw [if_neg h1]
            have hq1_ne_p1 : q.val.1 ≠ p.val.1 := fun h => h1 (Or.inl h)
            have hs : some q.val.1 ≠ some p.val.1 := fun h => hq1_ne_p1 (Option.some.inj h)
            rw [if_neg hs]
            split_ifs <;> decide
        · dsimp only [d, c]
          by_cases h1 : q.val.1 = p.val.1 ∨ q.val.2 = p.val.1
          · rw [if_pos h1]
            have hq2_ne_p2 : q.val.2 ≠ p.val.2 := by
              intro h
              rcases h1 with h1 | h1
              · apply hqp
                exact Subtype.ext (Prod.ext h1 h)
              · exact hp12 (h1.symm.trans h)
            have hs : some q.val.2 ≠ some p.val.2 := fun h => hq2_ne_p2 (Option.some.inj h)
            rw [if_neg hs]
            split_ifs <;> decide
          · rw [if_neg h1]
            have hq2_ne_p1 : q.val.2 ≠ p.val.1 := fun h => h1 (Or.inr h)
            have hs : some q.val.2 ≠ some p.val.1 := fun h => hq2_ne_p1 (Option.some.inj h)
            rw [if_neg hs]
            split_ifs <;> decide
      · dsimp only [c]; simp
      · dsimp only [c]; simp [hp12.symm]
      · dsimp only [c]; simp [hp12.symm]
  refine ⟨hpart1, hpart2, ?_⟩
  intro b summary answer hans
  have hinj : Function.Injective summary := by
    intro E1 E2 heq
    funext p
    have h1 : answer (summary E1) p = true ↔ E1 p = false := (hans E1 p).trans (hpart2 E1 p)
    have h2 : answer (summary E2) p = true ↔ E2 p = false := (hans E2 p).trans (hpart2 E2 p)
    rw [heq] at h1
    have hiff : E1 p = false ↔ E2 p = false := h1.symm.trans h2
    cases hE1 : E1 p <;> cases hE2 : E2 p <;> simp_all
  have hcard := Fintype.card_le_of_injective summary hinj
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  rw [card_pair k] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard

end PEqualNP.Outside.L_pcx_476

theorem PEqualNP.Outside.L_pcx_476 : (∀ k : Nat,
  let Pair := {p : Fin k × Fin k // p.1 < p.2}
  let extendsToHost := fun (E : Pair → Bool) (c : Option (Fin k) → Fin 3) =>
    ∃ d : Pair → Fin 3, ∀ p, E p = true →
      d p ≠ c none ∧ d p ≠ c (some p.val.1) ∧ d p ≠ c (some p.val.2)
  let query := fun (E : Pair → Bool) (p : Pair) =>
    ∃ c : Option (Fin k) → Fin 3, extendsToHost E c ∧
      c none ≠ c (some p.val.1) ∧ c none ≠ c (some p.val.2) ∧
      c (some p.val.1) ≠ c (some p.val.2)
  (∀ (E : Pair → Bool) (u v : Option (Fin k)), u ≠ v →
    ∀ a b : Fin 3, ∃ c : Option (Fin k) → Fin 3,
      extendsToHost E c ∧ c u = a ∧ c v = b) ∧
  (∀ (E : Pair → Bool) (p : Pair), query E p ↔ E p = false) ∧
  (∀ (b : Nat) (summary : (Pair → Bool) → (Fin b → Bool))
    (answer : (Fin b → Bool) → Pair → Bool),
    (∀ E p, answer (summary E) p = true ↔ query E p) → Nat.choose k 2 ≤ b)) :=
  PEqualNP.Outside.L_pcx_476.main_proof
