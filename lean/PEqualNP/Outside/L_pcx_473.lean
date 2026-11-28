import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset

namespace PEqualNP.Outside.L_pcx_473

-- A finite family of sets closed under union and intersection, whose strictly
-- nested members differ in at least m elements and whose nested members differ
-- in at most k elements, has at most 2 ^ (k / m) members.
theorem ring_bound {β : Type*} [DecidableEq β] (m : ℕ) (hm : 0 < m) :
    ∀ (s k : ℕ) (R : Finset (Finset β)), R.card ≤ s →
      (∀ X ∈ R, ∀ Y ∈ R, X ∪ Y ∈ R) → (∀ X ∈ R, ∀ Y ∈ R, X ∩ Y ∈ R) →
      (∀ X ∈ R, ∀ Y ∈ R, X ⊂ Y → m ≤ (Y \ X).card) →
      (∀ X ∈ R, ∀ Y ∈ R, X ⊆ Y → (Y \ X).card ≤ k) → R.card ≤ 2 ^ (k / m) := by
  intro s
  induction s with
  | zero =>
    intro k R hR _ _ _ _
    have : 0 < 2 ^ (k / m) := Nat.two_pow_pos _
    omega
  | succ s ih =>
    intro k R hR hU hI hS hK
    by_cases h1 : R.card ≤ 1
    · exact h1.trans Nat.one_le_two_pow
    push Not at h1
    have hne : R.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨X0, hX0, hmin0⟩ := Finset.exists_min_image R Finset.card hne
    have hbot : ∀ Y ∈ R, X0 ⊆ Y := by
      intro Y hY
      have h := hmin0 _ (hI X0 hX0 Y hY)
      have : X0 ∩ Y = X0 := Finset.eq_of_subset_of_card_le Finset.inter_subset_left h
      rw [← this]
      exact Finset.inter_subset_right
    have hne' : (R.erase X0).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hX0]
      omega
    obtain ⟨X1, hX1', hmin1⟩ := Finset.exists_min_image (R.erase X0) Finset.card hne'
    have hX1 : X1 ∈ R := Finset.mem_of_mem_erase hX1'
    have hX10 : X1 ≠ X0 := Finset.ne_of_mem_erase hX1'
    have h01s : X0 ⊆ X1 := hbot X1 hX1
    have h01 : X0 ⊂ X1 := Finset.ssubset_iff_subset_ne.mpr ⟨h01s, hX10.symm⟩
    have hsplit : ∀ Y ∈ R, ¬ X1 ⊆ Y → Y ∩ X1 = X0 := by
      intro Y hY hn
      by_contra hc
      have hm1 := hmin1 _ (Finset.mem_erase.mpr ⟨hc, hI Y hY X1 hX1⟩)
      have : Y ∩ X1 = X1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right hm1
      apply hn
      rw [← this]
      exact Finset.inter_subset_left
    have hcard := Finset.card_filter_add_card_filter_not (s := R) (fun Y => X1 ⊆ Y)
    have h01c : (R.filter (fun Y => ¬ X1 ⊆ Y)).card ≤ (R.filter (fun Y => X1 ⊆ Y)).card := by
      apply Finset.card_le_card_of_injOn (fun Y => Y ∪ X1)
      · intro Y hY
        rw [Finset.mem_coe, Finset.mem_filter] at hY
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨hU Y hY.1 X1 hX1, Finset.subset_union_right⟩
      · intro Y hY Y' hY' heq
        rw [Finset.mem_coe, Finset.mem_filter] at hY hY'
        have e1 := hsplit Y hY.1 hY.2
        have e2 := hsplit Y' hY'.1 hY'.2
        have heq' : Y ∪ X1 = Y' ∪ X1 := heq
        ext v
        by_cases hv : v ∈ X1
        · have a1 : v ∈ Y ∩ X1 ↔ v ∈ Y' ∩ X1 := by rw [e1, e2]
          simp only [Finset.mem_inter] at a1
          tauto
        · have a1 : v ∈ Y ∪ X1 ↔ v ∈ Y' ∪ X1 := by rw [heq']
          simp only [Finset.mem_union] at a1
          tauto
    have hlt : (R.filter (fun Y => X1 ⊆ Y)).card < R.card := by
      apply Finset.card_lt_card
      rw [Finset.filter_ssubset]
      refine ⟨X0, hX0, fun h => ?_⟩
      exact hX10 (Finset.Subset.antisymm h h01s)
    have hkm : m ≤ k := (hS X0 hX0 X1 hX1 h01).trans (hK X0 hX0 X1 hX1 h01s)
    have hIH := ih (k - m) (R.filter (fun Y => X1 ⊆ Y)) (by omega)
      (by
        intro X hX Y hY
        rw [Finset.mem_filter] at hX hY ⊢
        exact ⟨hU X hX.1 Y hY.1, hX.2.trans Finset.subset_union_left⟩)
      (by
        intro X hX Y hY
        rw [Finset.mem_filter] at hX hY ⊢
        exact ⟨hI X hX.1 Y hY.1, Finset.subset_inter hX.2 hY.2⟩)
      (by
        intro X hX Y hY hXY
        rw [Finset.mem_filter] at hX hY
        exact hS X hX.1 Y hY.1 hXY)
      (by
        intro X hX Y hY hXY
        rw [Finset.mem_filter] at hX hY
        have c1 := Finset.card_sdiff_of_subset hXY
        have c2 := Finset.card_sdiff_of_subset (hbot Y hY.1)
        have c3 := Finset.card_sdiff_of_subset h01s
        have c4 := Finset.card_le_card hX.2
        have c5 := Finset.card_le_card hXY
        have c6 := Finset.card_le_card h01s
        have c7 := hK X0 hX0 Y hY.1 (hbot Y hY.1)
        have c8 := hS X0 hX0 X1 hX1 h01
        omega)
    rw [Nat.div_eq_sub_div hm hkm, pow_succ]
    omega

-- propositional bookkeeping for the two mixtures
theorem flip_aux (a b : Prop) (h : a → b) (hn : ¬ (a ↔ b)) : b ∧ ¬ a := by
  by_cases ha : a
  · exact absurd ⟨fun _ => h ha, fun _ => ha⟩ hn
  · exact ⟨by by_contra hb; exact hn ⟨fun x => absurd x ha, fun x => absurd x hb⟩, ha⟩
theorem cover_aux (a1 a2 b1 b2 d1 d2 s1 s2 : Prop) [Decidable s1] [Decidable s2]
    (h1 : a1 ∨ a2) (h2 : b1 ∨ b2) (k1 : d1 → (a1 ↔ b1)) (k2 : d2 → (a2 ↔ b2))
    (k3 : ¬d1 → ¬d2 → (s1 ↔ ¬ s2)) :
    ((if s1 then a1 ∧ b1 else a1 ∨ b1) ∨ (if s2 then a2 ∧ b2 else a2 ∨ b2)) ∧
    ((if s1 then a1 ∨ b1 else a1 ∧ b1) ∨ (if s2 then a2 ∨ b2 else a2 ∧ b2)) := by
  by_cases q1 : a1 ∧ b1
  · constructor <;> left <;> split_ifs <;> first | exact q1 | exact Or.inl q1.1
  by_cases q2 : a2 ∧ b2
  · constructor <;> right <;> split_ifs <;> first | exact q2 | exact Or.inl q2.1
  have o1 : a1 ∨ b1 := by tauto
  have o2 : a2 ∨ b2 := by tauto
  have n1 : ¬ d1 := fun d => q1 (by have := k1 d; tauto)
  have n2 : ¬ d2 := fun d => q2 (by have := k2 d; tauto)
  have k := k3 n1 n2
  by_cases s : s1
  · have s' : ¬ s2 := k.mp s
    exact ⟨Or.inr (by simp only [s', ↓reduceIte]; exact o2), Or.inl (by simp only [s, ↓reduceIte]; exact o1)⟩
  · have s' : s2 := by by_contra hs2; exact s (k.mpr hs2)
    exact ⟨Or.inl (by simp only [s, ↓reduceIte]; exact o1), Or.inr (by simp only [s', ↓reduceIte]; exact o2)⟩
theorem pin_aux (a b s : Prop) [Decidable s] (h : a ∧ b) :
    (if s then a ∧ b else a ∨ b) ∧ (if s then a ∨ b else a ∧ b) := by
  split_ifs
  · exact ⟨h, Or.inl h.1⟩
  · exact ⟨Or.inl h.1, h⟩
theorem out_aux (a b s : Prop) [Decidable s] (ha : ¬ a) (hb : ¬ b) :
    ¬ (if s then a ∧ b else a ∨ b) ∧ ¬ (if s then a ∨ b else a ∧ b) := by
  split_ifs <;> tauto
theorem z_aux (a b s d : Prop) [Decidable s] (k : d → (a ↔ b)) :
    (((if s then a ∧ b else a ∨ b) ∧ d) ↔ a ∧ d) ∧ (((if s then a ∨ b else a ∧ b) ∧ d) ↔ a ∧ d) := by
  by_cases hd : d
  · have := k hd
    split_ifs <;> tauto
  · tauto
theorem t_aux (a b s d : Prop) [Decidable s] :
    ((¬ d ∧ ((if s then a ∧ b else a ∨ b) ↔ ¬ s)) ↔ ((¬ d ∧ (a ↔ ¬ s)) ∨ (¬ d ∧ (b ↔ ¬ s)))) ∧
    ((¬ d ∧ ((if s then a ∨ b else a ∧ b) ↔ ¬ s)) ↔ ((¬ d ∧ (a ↔ ¬ s)) ∧ (¬ d ∧ (b ↔ ¬ s)))) := by
  split_ifs <;> tauto

end PEqualNP.Outside.L_pcx_473

theorem PEqualNP.Outside.L_pcx_473 :
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    ∀ (n h N : Nat) (A : Finset (Equiv.Perm (Fin n)))
      (G : Finset (Fin N × Fin N)) (w : Fin N → Nat)
      (p : Fin n → Fin n → Fin N) (D S I O : Finset (Fin N)),
      0 < h →
      (∀ σ ∈ A, ∀ τ ∈ A, σ ≠ τ →
        h ≤ (Finset.univ.filter (fun i : Fin n => σ i ≠ τ i)).card) →
      (∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)) →
      let cover := fun (C : Finset (Fin N)) => ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
      let selected := fun (C : Finset (Fin N)) =>
        cover C ∧ (∀ B, cover B → C.sum w ≤ B.sum w) ∧ I ⊆ C ∧ Disjoint O C
      let reads := fun (C : Finset (Fin N)) (σ : Equiv.Perm (Fin n)) =>
        ∀ i j, p i j ∈ C ↔ σ i = j
      (∀ C, selected C → ∃ σ ∈ A, reads C σ) →
      (∀ σ ∈ A, ∃ C, selected C ∧ reads C σ) →
      (∀ Z ∈ D.powerset,
        (A.filter (fun σ => ∃ C, selected C ∧ C ∩ D = Z ∧ reads C σ)).card ≤
          2 ^ (n / h)) ∧
      A.card ≤ 2 ^ (D.card + n / h) := by
  intro n h N A G w p D S I O hh hdist hbip cover selected reads hsel hA
  classical
  have key : ∀ Z : Finset (Fin N),
      (A.filter (fun σ => ∃ C, selected C ∧ C ∩ D = Z ∧ reads C σ)).card ≤ 2 ^ (n / h) := by
    intro Z
    let τ : Finset (Fin N) → Finset (Fin n × Fin n) := fun C =>
      Finset.univ.filter (fun c => p c.1 c.2 ∉ D ∧ (p c.1 c.2 ∈ C ↔ p c.1 c.2 ∉ S))
    let F := (Finset.univ : Finset (Finset (Fin N))).filter (fun C => selected C ∧ C ∩ D = Z)
    have memF : ∀ C, C ∈ F ↔ selected C ∧ C ∩ D = Z := by
      intro C
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    have memZ : ∀ C, C ∩ D = Z → ∀ v ∈ D, (v ∈ C ↔ v ∈ Z) := by
      intro C hC v hv
      rw [← hC, Finset.mem_inter]
      tauto
    have memτ : ∀ C c, c ∈ τ C ↔ (p c.1 c.2 ∉ D ∧ (p c.1 c.2 ∈ C ↔ p c.1 c.2 ∉ S)) := by
      intro C c
      simp only [τ, Finset.mem_filter, Finset.mem_univ, true_and]
    have cellflip : ∀ C ∈ F, ∀ C' ∈ F, ∀ σ σ', reads C σ → reads C' σ' →
        ∀ c : Fin n × Fin n, ((c ∈ τ C ↔ c ∈ τ C') ↔ (σ c.1 = c.2 ↔ σ' c.1 = c.2)) := by
      intro C hC C' hC' σ σ' hr hr' c
      have e1 := hr c.1 c.2
      have e2 := hr' c.1 c.2
      rw [memτ, memτ, ← e1, ← e2]
      by_cases hv : p c.1 c.2 ∈ D
      · have h1 := memZ C ((memF C).mp hC).2 _ hv
        have h2 := memZ C' ((memF C').mp hC').2 _ hv
        tauto
      · tauto
    have closed : ∀ C ∈ F, ∀ C' ∈ F, (∃ M ∈ F, τ M = τ C ∪ τ C') ∧ (∃ M ∈ F, τ M = τ C ∩ τ C') := by
      intro C hC C' hC'
      obtain ⟨⟨hcov, hmin, hI, hO⟩, hZ⟩ := (memF C).mp hC
      obtain ⟨⟨hcov', hmin', hI', hO'⟩, hZ'⟩ := (memF C').mp hC'
      have hD : ∀ v ∈ D, (v ∈ C ↔ v ∈ C') := fun v hv =>
        (memZ C hZ v hv).trans (memZ C' hZ' v hv).symm
      let M1 := (Finset.univ : Finset (Fin N)).filter
        (fun v => if v ∈ S then (v ∈ C ∧ v ∈ C') else (v ∈ C ∨ v ∈ C'))
      let M2 := (Finset.univ : Finset (Fin N)).filter
        (fun v => if v ∈ S then (v ∈ C ∨ v ∈ C') else (v ∈ C ∧ v ∈ C'))
      have m1 : ∀ v, v ∈ M1 ↔ (if v ∈ S then (v ∈ C ∧ v ∈ C') else (v ∈ C ∨ v ∈ C')) := by
        intro v
        simp only [M1, Finset.mem_filter, Finset.mem_univ, true_and]
      have m2 : ∀ v, v ∈ M2 ↔ (if v ∈ S then (v ∈ C ∨ v ∈ C') else (v ∈ C ∧ v ∈ C')) := by
        intro v
        simp only [M2, Finset.mem_filter, Finset.mem_univ, true_and]
      have cov1 : cover M1 := by
        intro e he
        have h1 := hcov e he
        have h2 := hcov' e he
        have k1 := hD e.1
        have k2 := hD e.2
        have k3 := hbip e he
        rw [m1, m1]
        exact (PEqualNP.Outside.L_pcx_473.cover_aux _ _ _ _ _ _ _ _ h1 h2 k1 k2 (k3)).1
      have cov2 : cover M2 := by
        intro e he
        have h1 := hcov e he
        have h2 := hcov' e he
        have k1 := hD e.1
        have k2 := hD e.2
        have k3 := hbip e he
        rw [m2, m2]
        exact (PEqualNP.Outside.L_pcx_473.cover_aux _ _ _ _ _ _ _ _ h1 h2 k1 k2 (k3)).2
      have sumC : ∀ T : Finset (Fin N), T.sum w = ∑ v, if v ∈ T then w v else 0 := by
        intro T
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      have wsum : M1.sum w + M2.sum w = C.sum w + C'.sum w := by
        rw [sumC M1, sumC M2, sumC C, sumC C', ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _
        by_cases a : v ∈ S <;> by_cases b : v ∈ C <;> by_cases c : v ∈ C' <;> simp [m1, m2, a, b, c]
      have b1 := hmin M1 cov1
      have b2 := hmin M2 cov2
      have b3 := hmin' C hcov
      have sel1 : selected M1 := by
        refine ⟨cov1, fun B hB => ?_, fun v hv => ?_, Finset.disjoint_left.mpr (fun v hv => ?_)⟩
        · have := hmin B hB
          omega
        · have a1 := hI hv
          have a2 := hI' hv
          rw [m1]
          exact (PEqualNP.Outside.L_pcx_473.pin_aux _ _ _ ⟨a1, a2⟩).1
        · have a1 := Finset.disjoint_left.mp hO hv
          have a2 := Finset.disjoint_left.mp hO' hv
          rw [m1]
          exact (PEqualNP.Outside.L_pcx_473.out_aux _ _ _ a1 a2).1
      have sel2 : selected M2 := by
        refine ⟨cov2, fun B hB => ?_, fun v hv => ?_, Finset.disjoint_left.mpr (fun v hv => ?_)⟩
        · have := hmin B hB
          omega
        · have a1 := hI hv
          have a2 := hI' hv
          rw [m2]
          exact (PEqualNP.Outside.L_pcx_473.pin_aux _ _ _ ⟨a1, a2⟩).2
        · have a1 := Finset.disjoint_left.mp hO hv
          have a2 := Finset.disjoint_left.mp hO' hv
          rw [m2]
          exact (PEqualNP.Outside.L_pcx_473.out_aux _ _ _ a1 a2).2
      have z1 : M1 ∩ D = Z := by
        rw [← hZ]
        ext v
        rw [Finset.mem_inter, Finset.mem_inter, m1]
        exact (PEqualNP.Outside.L_pcx_473.z_aux _ _ _ _ (hD v)).1
      have z2 : M2 ∩ D = Z := by
        rw [← hZ]
        ext v
        rw [Finset.mem_inter, Finset.mem_inter, m2]
        exact (PEqualNP.Outside.L_pcx_473.z_aux _ _ _ _ (hD v)).2
      refine ⟨⟨M1, (memF M1).mpr ⟨sel1, z1⟩, ?_⟩, ⟨M2, (memF M2).mpr ⟨sel2, z2⟩, ?_⟩⟩
      · ext c
        rw [Finset.mem_union, memτ, memτ, memτ, m1]
        exact (PEqualNP.Outside.L_pcx_473.t_aux _ _ _ _).1
      · ext c
        rw [Finset.mem_inter, memτ, memτ, memτ, m2]
        exact (PEqualNP.Outside.L_pcx_473.t_aux _ _ _ _).2
    have hread : ∀ C ∈ F, ∃ σ ∈ A, reads C σ := fun C hC => hsel C ((memF C).mp hC).1
    let R := F.image τ
    have hR : R.card ≤ 2 ^ ((2 * n) / (2 * h)) := by
      apply PEqualNP.Outside.L_pcx_473.ring_bound (2 * h) (by omega) R.card (2 * n) R le_rfl
      · intro X hX Y hY
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hX
        obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hY
        obtain ⟨M, hM, e⟩ := (closed C hC C' hC').1
        rw [← e]
        exact Finset.mem_image_of_mem τ hM
      · intro X hX Y hY
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hX
        obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hY
        obtain ⟨M, hM, e⟩ := (closed C hC C' hC').2
        rw [← e]
        exact Finset.mem_image_of_mem τ hM
      · intro X hX Y hY hXY
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hX
        obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hY
        obtain ⟨σ, hσ, hr⟩ := hread C hC
        obtain ⟨σ', hσ', hr'⟩ := hread C' hC'
        have hfl := cellflip C hC C' hC' σ σ' hr hr'
        have hne : σ ≠ σ' := by
          intro hs
          subst hs
          apply (Finset.ssubset_iff_subset_ne.mp hXY).2
          ext c
          exact (hfl c).mpr Iff.rfl
        have hd : h ≤ (Finset.univ.filter (fun i : Fin n => σ i ≠ σ' i)).card := by
          convert hdist σ hσ σ' hσ' hne
        have hsub := (Finset.ssubset_iff_subset_ne.mp hXY).1
        let f : Fin n × Bool → Fin n × Fin n := fun q => (q.1, if q.2 then σ' q.1 else σ q.1)
        have hc := Finset.card_le_card_of_injOn f
          (s := (Finset.univ.filter (fun i : Fin n => σ i ≠ σ' i)) ×ˢ (Finset.univ : Finset Bool))
          (t := τ C' \ τ C) ?_ ?_
        · rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hc
          omega
        · intro q hq
          rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter] at hq
          rw [Finset.mem_coe, Finset.mem_sdiff]
          have hq1 : σ q.1 ≠ σ' q.1 := hq.1.2
          have e := hfl (f q)
          apply PEqualNP.Outside.L_pcx_473.flip_aux _ _ (fun a => hsub a)
          intro hh
          have e3 := e.mp hh
          rcases q with ⟨i, b⟩
          cases b
          · dsimp only [f] at e3 hq1
            simp only [Bool.false_eq_true, ↓reduceIte] at e3
            exact hq1 (e3.mp trivial).symm
          · dsimp only [f] at e3 hq1
            simp only [↓reduceIte] at e3
            exact hq1 (e3.mpr trivial)
        · intro q hq q' hq' e
          rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter] at hq hq'
          have hq1 : σ q.1 ≠ σ' q.1 := hq.1.2
          rcases q with ⟨i, b⟩
          rcases q' with ⟨i', b'⟩
          dsimp only [f] at e hq1
          rw [Prod.mk.injEq] at e
          obtain ⟨rfl, e2⟩ := e
          cases b <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte] at e2
          · rfl
          · exact absurd e2 hq1
          · exact absurd e2.symm hq1
          · rfl
      · intro X hX Y hY hXY
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hX
        obtain ⟨C', hC', rfl⟩ := Finset.mem_image.mp hY
        obtain ⟨σ, hσ, hr⟩ := hread C hC
        obtain ⟨σ', hσ', hr'⟩ := hread C' hC'
        have hfl := cellflip C hC C' hC' σ σ' hr hr'
        let f : Fin n × Bool → Fin n × Fin n := fun q => (q.1, if q.2 then σ' q.1 else σ q.1)
        have hs : τ C' \ τ C ⊆ (Finset.univ : Finset (Fin n × Bool)).image f := by
          intro c hc
          rw [Finset.mem_sdiff] at hc
          have e := hfl c
          rw [Finset.mem_image]
          by_cases h1 : σ c.1 = c.2
          · refine ⟨(c.1, false), Finset.mem_univ _, ?_⟩
            simp only [f, Bool.false_eq_true, ite_false]
            rw [h1]
          · have h2 : σ' c.1 = c.2 := by tauto
            refine ⟨(c.1, true), Finset.mem_univ _, ?_⟩
            simp only [f, ite_true]
            rw [h2]
        have := (Finset.card_le_card hs).trans Finset.card_image_le
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at this
        omega
    rw [Nat.mul_div_mul_left n h Nat.two_pos] at hR
    refine le_trans ?_ hR
    let g : Equiv.Perm (Fin n) → Finset (Fin n × Fin n) := fun σ =>
      if hσ : ∃ C, selected C ∧ C ∩ D = Z ∧ reads C σ then τ (Classical.choose hσ) else ∅
    apply Finset.card_le_card_of_injOn g
    · intro σ hσ
      rw [Finset.mem_coe, Finset.mem_filter] at hσ
      rw [Finset.mem_coe]
      simp only [g, hσ.2, ↓reduceDIte]
      obtain ⟨h1, h2, _⟩ := Classical.choose_spec hσ.2
      exact Finset.mem_image_of_mem τ ((memF _).mpr ⟨h1, h2⟩)
    · intro σ1 hσ1 σ2 hσ2 e
      rw [Finset.mem_coe, Finset.mem_filter] at hσ1 hσ2
      simp only [g, hσ1.2, hσ2.2, ↓reduceDIte] at e
      obtain ⟨a1, a2, a3⟩ := Classical.choose_spec hσ1.2
      obtain ⟨b1, b2, b3⟩ := Classical.choose_spec hσ2.2
      have hfl := cellflip _ ((memF _).mpr ⟨a1, a2⟩) _ ((memF _).mpr ⟨b1, b2⟩) σ1 σ2 a3 b3
      ext i
      have := (hfl (i, σ1 i)).mp (by rw [e])
      simp only at this
      exact congrArg Fin.val (this.mp trivial).symm
  refine ⟨fun Z _ => by convert key Z, ?_⟩
  have hsub : A ⊆ D.powerset.biUnion
      (fun Z => A.filter (fun σ => ∃ C, selected C ∧ C ∩ D = Z ∧ reads C σ)) := by
    intro σ hσ
    obtain ⟨C, hC, hr⟩ := hA σ hσ
    rw [Finset.mem_biUnion]
    exact ⟨C ∩ D, Finset.mem_powerset.mpr Finset.inter_subset_right,
      Finset.mem_filter.mpr ⟨hσ, C, hC, rfl, hr⟩⟩
  calc A.card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ Z ∈ D.powerset,
        (A.filter (fun σ => ∃ C, selected C ∧ C ∩ D = Z ∧ reads C σ)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ Z ∈ D.powerset, 2 ^ (n / h) := Finset.sum_le_sum (fun Z _ => key Z)
    _ = 2 ^ (D.card + n / h) := by
      rw [Finset.sum_const, Finset.card_powerset, pow_add]
      rfl
