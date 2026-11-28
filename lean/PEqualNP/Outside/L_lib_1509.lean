import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1509_aux

open scoped BigOperators
open scoped Classical

private def vc {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) : Prop :=
  ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
private def minimum {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat)
    (C : Finset (Fin N)) : Prop := vc G C ∧ ∀ B, vc G B → C.sum w ≤ B.sum w
private def shores {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) : Prop :=
  ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
private noncomputable def projection {V : Type} [Fintype V] {N : Nat} (p : V → Fin N)
    (C : Finset (Fin N)) : Finset V :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  Finset.univ.filter (fun j => p j ∈ C)
private def hits {m k : Nat} (A : Fin m → Finset (Fin k)) (X : Finset (Fin m × Fin k)) : Prop :=
  ∀ i, ∃ j ∈ A i, (i,j) ∈ X

private lemma mix_step (a b c d s t x y : Prop) [Decidable s] [Decidable t]
    (h₁ : a ∨ b) (h₂ : c ∨ d) (hx : x → (a ↔ c)) (hy : y → (b ↔ d))
    (hst : ¬ x → ¬ y → (s ↔ ¬ t)) :
    ((if s then a ∧ c else a ∨ c) ∨ (if t then b ∧ d else b ∨ d)) ∧
    ((if s then a ∨ c else a ∧ c) ∨ (if t then b ∨ d else b ∧ d)) := by
  by_cases hs : s <;> by_cases ht : t <;> simp only [hs, ht, ite_true, ite_false] <;> tauto

private lemma mix_minimum {N : Nat} {G : Finset (Fin N × Fin N)} {w : Fin N → Nat}
    {D S B C : Finset (Fin N)} (hs : shores G D S)
    (hb : minimum G w B) (hc : minimum G w C) (hd : B ∩ D = C ∩ D) :
    minimum G w ((B ∪ C).filter fun v => if v ∈ S then v ∈ B ∧ v ∈ C else True) := by
  let M := (B ∪ C).filter fun v => if v ∈ S then v ∈ B ∧ v ∈ C else True
  let R := (B ∪ C).filter fun v => if v ∈ S then True else v ∈ B ∧ v ∈ C
  have hm v : v ∈ M ↔ if v ∈ S then v ∈ B ∧ v ∈ C else v ∈ B ∨ v ∈ C := by
    by_cases h : v ∈ S <;> simp [M, h] <;> tauto
  have hr v : v ∈ R ↔ if v ∈ S then v ∈ B ∨ v ∈ C else v ∈ B ∧ v ∈ C := by
    by_cases h : v ∈ S <;> simp [R, h] <;> tauto
  have hd' v (hv : v ∈ D) : v ∈ B ↔ v ∈ C := by
    have h := Finset.ext_iff.mp hd v
    simpa [hv] using h
  have hcover : vc G M ∧ vc G R := by
    have step (e : Fin N × Fin N) (he : e ∈ G) :
        (e.1 ∈ M ∨ e.2 ∈ M) ∧ (e.1 ∈ R ∨ e.2 ∈ R) := by
      rw [hm, hm, hr, hr]
      exact mix_step _ _ _ _ _ _ _ _ (hb.1 e he) (hc.1 e he) (hd' e.1) (hd' e.2) (hs e he)
    exact ⟨fun e he => (step e he).1, fun e he => (step e he).2⟩
  have hi : M ∩ R = B ∩ C := by
    ext v
    simp only [Finset.mem_inter, hm, hr]
    by_cases h : v ∈ S <;> simp only [h, if_true, if_false] <;> tauto
  have hu : M ∪ R = B ∪ C := by
    ext v
    simp only [Finset.mem_union, hm, hr]
    by_cases h : v ∈ S <;> simp only [h, if_true, if_false] <;> tauto
  have hsum : M.sum w + R.sum w = B.sum w + C.sum w := by
    calc
      _ = (M ∪ R).sum w + (M ∩ R).sum w := (Finset.sum_union_inter (f := w)).symm
      _ = (B ∪ C).sum w + (B ∩ C).sum w := by rw [hi, hu]
      _ = _ := Finset.sum_union_inter (f := w)
  change minimum G w M
  have hMR := hb.2 M hcover.1
  have hRC := hc.2 R hcover.2
  exact ⟨hcover.1, fun K hK => by have := hb.2 K hK; omega⟩

private lemma lower {m k d N : Nat} (A : Fin m → Finset (Fin k))
    (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (p : Fin m × Fin k → Fin N)
    (D S : Finset (Fin N)) (hd : D.card ≤ d) (hs : shores G D S)
    (hh : ∀ X, hits A X ↔ ∃ C, minimum G w C ∧ projection p C = X) :
    (∏ i, ((A i).card + 1) / 2) ≤ 2 ^ d := by
  let L (i : Fin m) := (A i).filter fun j => p (i,j) ∈ S
  let R (i : Fin m) := (A i).filter fun j => p (i,j) ∉ S
  let T (i : Fin m) := if (R i).card ≤ (L i).card then L i else R i
  have hcard i : ((A i).card + 1) / 2 ≤ (T i).card := by
    have hf : (L i).card + (R i).card = (A i).card := Finset.card_filter_add_card_filter_not _
    unfold T
    split <;> omega
  let W := (i : Fin m) → {j // j ∈ T i}
  let pattern (f : W) : Finset (Fin m × Fin k) := Finset.univ.image (fun i => (i,(f i).1))
  have hp (f : W) (i : Fin m) (j : Fin k) : (i,j) ∈ pattern f ↔ j = (f i).1 := by
    simp only [pattern, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq]
    exact ⟨fun ⟨a, h, hj⟩ => by subst a; exact hj.symm, fun h => ⟨i, rfl, h.symm⟩⟩
  have ht (f : W) : hits A (pattern f) := by
    intro i
    refine ⟨(f i).1, ?_, (hp f i _).2 rfl⟩
    have h := (f i).2
    unfold T at h
    split at h <;> exact (Finset.mem_filter.mp h).1
  choose lift hl hr using fun f : W => (hh _).mp (ht f)
  have hmem f i j : p (i,j) ∈ lift f ↔ j = (f i).1 := by
    rw [← hp f i j, ← hr f]
    simp [projection]
  have inj : Function.Injective (fun f : W => (⟨lift f ∩ D,
      Finset.mem_powerset.mpr Finset.inter_subset_right⟩ : {U // U ∈ D.powerset})) := by
    intro f g he
    funext i
    apply Subtype.ext
    by_contra hne
    have hd' : lift f ∩ D = lift g ∩ D := congrArg Subtype.val he
    by_cases h : (R i).card ≤ (L i).card
    · have hM := mix_minimum hs (hl f) (hl g) hd'
      obtain ⟨j, hj, hjM⟩ := (hh _).mpr ⟨_, hM, rfl⟩ i
      simp only [projection, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hjM
      have hj' : j = (f i).1 ∨ j = (g i).1 := by
        simpa only [hmem] using hjM.1
      have hs' : p (i,j) ∈ S := by
        rcases hj' with rfl | rfl
        · exact (Finset.mem_filter.mp (show (f i).1 ∈ L i by simpa [T, h] using (f i).2)).2
        · exact (Finset.mem_filter.mp (show (g i).1 ∈ L i by simpa [T, h] using (g i).2)).2
      simp only [hs', if_true, hmem] at hjM
      exact hne (hjM.2.1.symm.trans hjM.2.2)
    · have hM := mix_minimum (S := Finset.univ \ S) (by
        intro e he h₁ h₂
        simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using (hs e he h₁ h₂).not) (hl f) (hl g) hd'
      obtain ⟨j, hj, hjM⟩ := (hh _).mpr ⟨_, hM, rfl⟩ i
      simp only [projection, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hjM
      have hj' : j = (f i).1 ∨ j = (g i).1 := by
        simpa only [hmem] using hjM.1
      have hs' : p (i,j) ∈ Finset.univ \ S := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        rcases hj' with rfl | rfl
        · exact (Finset.mem_filter.mp (show (f i).1 ∈ R i by simpa [T, h] using (f i).2)).2
        · exact (Finset.mem_filter.mp (show (g i).1 ∈ R i by simpa [T, h] using (g i).2)).2
      simp only [hs', if_true, hmem] at hjM
      exact hne (hjM.2.1.symm.trans hjM.2.2)
  have hw := Fintype.card_le_of_injective _ inj
  simp only [W, Fintype.card_pi, Fintype.card_coe, Finset.card_powerset] at hw
  exact (Finset.prod_le_prod' fun i _ => hcard i).trans (hw.trans (Nat.pow_le_pow_right (by decide) hd))

-- Transfer a finite independent-set model to the ordered-edge cover convention.
set_option maxHeartbeats 800000 in
private lemma transport {V U : Type} [Fintype V] [Fintype U] (d : Nat)
    (E : U → U → Prop) (w : U → Nat) (port : V ↪ U) (del : Fin d ↪ U)
    (color : U → Bool) (target : Finset V → Prop)
    (hloop : ∀ u, ¬ E u u)
    (hcross : ∀ u v, E u v → (∀ a, del a ≠ u) → (∀ a, del a ≠ v) →
      color u ≠ color v)
    (hpos : ∀ u, 0 < w u)
    (hmodels :
      let ind := fun I : U → Prop => ∀ u v, E u v → I u → ¬ I v
      let val := fun I : U → Prop => ∑ u, if I u then w u else 0
      let best := fun I => ind I ∧ ∀ J, ind J → val J ≤ val I
      ∀ X, target X ↔ ∃ I, best I ∧ ∀ a, a ∈ X ↔ ¬ I (port a))
    (hunique :
      let ind := fun I : U → Prop => ∀ u v, E u v → I u → ¬ I v
      let val := fun I : U → Prop => ∑ u, if I u then w u else 0
      let best := fun I => ind I ∧ ∀ J, ind J → val J ≤ val I
      ∀ I J, best I → best J → (∀ a, I (port a) ↔ J (port a)) → I = J) :
    ∃ (N : Nat) (G : Finset (Fin N × Fin N)) (w' : Fin N → Nat)
      (p : V → Fin N) (D S : Finset (Fin N)), D.card ≤ d ∧ shores G D S ∧
      (∀ e ∈ G, e.1 < e.2) ∧
      (∀ X, target X ↔ ∃ C, minimum G w' C ∧ projection p C = X) ∧
      Function.Injective p ∧ (∀ v, 0 < w' v) ∧
      ∀ B C, minimum G w' B → minimum G w' C → projection p B = projection p C → B = C := by
  classical
  let N := Fintype.card U
  let f : U ≃ Fin N := Fintype.equivFin U
  let p (a : V) := f (port a)
  let D : Finset (Fin N) := Finset.univ.map (del.trans f.toEmbedding)
  let S : Finset (Fin N) := Finset.univ.filter (fun v => color (f.symm v) = true)
  let G : Finset (Fin N × Fin N) := Finset.univ.filter (fun z => z.1 < z.2 ∧
    (E (f.symm z.1) (f.symm z.2) ∨ E (f.symm z.2) (f.symm z.1)))
  let w' (v : Fin N) := w (f.symm v)
  let ind := fun I : U → Prop => ∀ u v, E u v → I u → ¬ I v
  let val := fun I : U → Prop => ∑ u, if I u then w u else 0
  let best := fun I => ind I ∧ ∀ J, ind J → val J ≤ val I
  let outside (C : Finset (Fin N)) (v : U) := f v ∉ C
  let ofPred (I : U → Prop) : Finset (Fin N) := Finset.univ.filter (fun v => ¬ I (f.symm v))
  have hG (e : Fin N × Fin N) : e ∈ G ↔ e.1 < e.2 ∧
      (E (f.symm e.1) (f.symm e.2) ∨ E (f.symm e.2) (f.symm e.1)) := by
    simp [G]
  have hI (I : U → Prop) : outside (ofPred I) = I := by
    funext u
    simp [outside, ofPred]
  have hcov (C : Finset (Fin N)) : vc G C ↔ ind (outside C) := by
    constructor
    · intro h u v huv hu hv
      have hne : f u ≠ f v := fun he => hloop u (by simpa only [← f.injective he] using huv)
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hc := h (f u, f v) ((hG _).2 ⟨hlt, Or.inl (by simpa using huv)⟩)
        exact hc.elim hu hv
      · have hc := h (f v, f u) ((hG _).2 ⟨hlt, Or.inr (by simpa using huv)⟩)
        exact hc.elim hv hu
    · intro h e he
      by_contra! hn
      rcases ((hG e).1 he).2 with hE | hE
      · exact h _ _ hE (by simpa [outside] using hn.1) (by simpa [outside] using hn.2)
      · exact h _ _ hE (by simpa [outside] using hn.2) (by simpa [outside] using hn.1)
  have hsum (C : Finset (Fin N)) : val (outside C) + C.sum w' = ∑ v, w' v := by
    have h₁ : val (outside C) = ∑ v : Fin N, if v ∉ C then w' v else 0 := by
      calc
        _ = ∑ u, if f u ∉ C then w' (f u) else 0 := by
          unfold val
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : f u ∈ C <;> simp [outside, w', hu]
        _ = _ := f.sum_comp (fun v : Fin N => if v ∉ C then w' v else 0)
    have h₂ : C.sum w' = ∑ v : Fin N, if v ∈ C then w' v else 0 := by
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp
    rw [h₁, h₂, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => by by_cases h : v ∈ C <;> simp [h])
  have hopt (C : Finset (Fin N)) : minimum G w' C ↔ best (outside C) := by
    constructor
    · intro h
      refine ⟨(hcov C).1 h.1, ?_⟩
      intro J hJ
      have hj : ind (outside (ofPred J)) := by rw [hI]; exact hJ
      have hw := h.2 (ofPred J) ((hcov _).2 hj)
      have hs := hsum (ofPred J)
      rw [hI] at hs
      have := hsum C
      omega
    · intro h
      refine ⟨(hcov C).2 h.1, ?_⟩
      intro B hB
      have hw := h.2 (outside B) ((hcov B).1 hB)
      have := hsum C
      have := hsum B
      omega
  have hproj (C : Finset (Fin N)) (a : V) :
      a ∈ projection p C ↔ ¬ outside C (port a) := by simp [projection, outside, p]
  refine ⟨N, G, w', p, D, S, by simp [D], ?_, ?_, ?_, f.injective.comp port.injective,
    fun v => hpos _, ?_⟩
  · intro e he h₁ h₂
    have hn₁ (a : Fin d) : del a ≠ f.symm e.1 := by
      intro hh
      apply h₁
      exact Finset.mem_map.mpr ⟨a, Finset.mem_univ _, by simp [hh]⟩
    have hn₂ (a : Fin d) : del a ≠ f.symm e.2 := by
      intro hh
      apply h₂
      exact Finset.mem_map.mpr ⟨a, Finset.mem_univ _, by simp [hh]⟩
    have hc := ((hG e).1 he).2.elim
      (fun h => hcross _ _ h hn₁ hn₂) (fun h => (hcross _ _ h hn₂ hn₁).symm)
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    cases hu : color (f.symm e.1) <;> cases hv : color (f.symm e.2) <;> simp [hu, hv] at hc ⊢
  · exact fun e he => ((hG e).1 he).1
  · intro X
    rw [hmodels]
    constructor
    · rintro ⟨I, hIbest, hX⟩
      refine ⟨ofPred I, (hopt _).2 (by rwa [hI]), ?_⟩
      ext a
      rw [hproj, hI, hX]
    · rintro ⟨C, hC, rfl⟩
      exact ⟨outside C, (hopt _).1 hC, hproj C⟩
  · intro B C hB hC hBC
    have hh := hunique (outside B) (outside C) ((hopt _).1 hB) ((hopt _).1 hC) (by
      intro a
      have hb := hproj B a
      have hc := hproj C a
      rw [hBC] at hb
      simpa only [not_not] using (hb.symm.trans hc).not)
    ext v
    have he := congrFun hh (f.symm v)
    simpa [outside] using not_congr (Iff.of_eq he)

-- Turn the unique label and unique independent-set extension into the cover model.
private lemma realization {V U L : Type} [Fintype V] [DecidableEq V] [Fintype U]
    (E : U → U → Prop) (w : U → Nat) (port : V ↪ U)
    (target : Finset V → Prop) (Sat : (V → Bool) → L → Prop)
    (state : (V → Bool) → L → U → Prop)
    (hport : ∀ x l v, state x l (port v) ↔ x v = false)
    (hsat : ∀ X, target X ↔ ∃! l, Sat (fun v => decide (v ∈ X)) l)
    (hexcl : ∀ x l j, Sat x l → Sat x j → l = j)
    (hbest :
      ∀ I : U → Prop,
        ((∀ u v, E u v → I u → ¬ I v) ∧
          ∀ J : U → Prop, (∀ u v, E u v → J u → ¬ J v) →
            (∑ u, if J u then w u else 0) ≤ (∑ u, if I u then w u else 0)) ↔
        ∃ x l, Sat x l ∧ I = state x l) :
    let ind := fun I : U → Prop => ∀ u v, E u v → I u → ¬ I v
    let val := fun I : U → Prop => ∑ u, if I u then w u else 0
    let best := fun I => ind I ∧ ∀ J, ind J → val J ≤ val I
    (∀ X, target X ↔ ∃ I, best I ∧ ∀ a, a ∈ X ↔ ¬ I (port a)) ∧
    (∀ I J, best I → best J → (∀ a, I (port a) ↔ J (port a)) → I = J) := by
  constructor
  · intro X
    constructor
    · intro ht
      obtain ⟨l, hl, _⟩ := (hsat X).1 ht
      refine ⟨state (fun v => decide (v ∈ X)) l, (hbest _).2 ⟨_, l, hl, rfl⟩, ?_⟩
      intro a
      rw [hport]
      by_cases ha : a ∈ X <;> simp [ha]
    · rintro ⟨I, hI, hX⟩
      obtain ⟨x, l, hl, rfl⟩ := (hbest I).1 hI
      have hx : (fun v => decide (v ∈ X)) = x := by
        funext v
        have hv := hX v
        rw [hport] at hv
        cases he : x v <;> simp_all
      apply (hsat X).2
      rw [hx]
      exact ⟨l, hl, fun j hj => hexcl x j l hj hl⟩
  · intro I J hI hJ hIJ
    obtain ⟨x, l, hl, rfl⟩ := (hbest I).1 hI
    obtain ⟨y, j, hj, rfl⟩ := (hbest J).1 hJ
    have hx : x = y := by
      funext v
      have hv := hIJ v
      rw [hport, hport] at hv
      cases hx : x v <;> cases hy : y v <;> simp [hx, hy] at hv ⊢
    subst y
    rw [hexcl x l j hl hj]

namespace PairPartition

open scoped BigOperators Classical

variable {m k d : Nat}

abbrev Input (m k : Nat) := Fin m × Fin k
abbrev Slot (m k : Nat) := Unit ⊕ (Input m k ⊕ Fin m)
abbrev Label (A : Fin m → Finset (Fin k)) := (i : Fin m) → Fin (((A i).card + 1) / 2)
abbrev PairRank (A : Fin m → Finset (Fin k)) (l : Label A) (i : Fin m) :=
  {r : Fin (A i).card // r.val / 2 = (l i).val}
abbrev Test (A : Fin m → Finset (Fin k)) (l : Label A) :=
  Unit ⊕ (Input m k ⊕ (Σ i, PairRank A l i))
abbrev Aux (A : Fin m → Finset (Fin k)) := Σ l : Label A, Test A l

variable (A : Fin m → Finset (Fin k))

private noncomputable def point (i : Fin m) (r : Fin (A i).card) : Input m k :=
  (i, ((A i).equivFin.symm r).val)

private noncomputable def rank (v : Input m k) : Nat :=
  if h : v.2 ∈ A v.1 then ((A v.1).equivFin ⟨v.2, h⟩).val else 0

private lemma point_mem (i : Fin m) (r : Fin (A i).card) :
    (point A i r).2 ∈ A (point A i r).1 := ((A i).equivFin.symm r).property

private lemma rank_point (i : Fin m) (r : Fin (A i).card) :
    rank A (point A i r) = r.val := by
  unfold rank
  rw [dif_pos (point_mem A i r)]
  exact congrArg Fin.val ((A i).equivFin.apply_symm_apply r)

private lemma point_rank (v : Input m k) (hv : v.2 ∈ A v.1) :
    point A v.1 ((A v.1).equivFin ⟨v.2, hv⟩) = v := by
  simp [point]

private lemma rank_eq_of_mem (v : Input m k) (hv : v.2 ∈ A v.1) :
    rank A v = ((A v.1).equivFin ⟨v.2, hv⟩).val := by simp [rank, hv]

private lemma card_le (hcount : (∏ i, ((A i).card + 1) / 2) ≤ 2 ^ d) :
    Fintype.card (Label A) ≤ Fintype.card (Fin d → Bool) := by
  rw [Fintype.card_pi_const, Fintype.card_bool]
  simpa only [Label, Fintype.card_pi, Fintype.card_fin] using hcount

private noncomputable def code (hcount : (∏ i, ((A i).card + 1) / 2) ≤ 2 ^ d)
    (l : Label A) : Fin d → Bool :=
  (Fintype.equivFin (Fin d → Bool)).symm (Fin.castLE (card_le A hcount) (Fintype.equivFin (Label A) l))

private lemma code_injective (hcount : (∏ i, ((A i).card + 1) / 2) ≤ 2 ^ d) :
    Function.Injective (code A hcount) := by
  intro l l' h
  have he := (Fintype.equivFin (Fin d → Bool)).symm.injective h
  exact (Fintype.equivFin (Label A)).injective (Fin.ext (congrArg (fun z => z.val) he))

noncomputable def col (v : Input m k) : Bool := decide (rank A v % 2 = 1)

def slot : Aux A → Slot m k
  | ⟨_, .inl _⟩ => .inl ()
  | ⟨_, .inr (.inl v)⟩ => .inr (.inl v)
  | ⟨_, .inr (.inr ⟨i, _⟩)⟩ => .inr (.inr i)

noncomputable def guard (hcount : (∏ i, ((A i).card + 1) / 2) ≤ 2 ^ d)
    (u : Aux A) : Fin d → Bool :=
  code A hcount u.1

noncomputable def shore : Aux A → Bool
  | ⟨_, .inl _⟩ => false
  | ⟨_, .inr (.inl v)⟩ => col A v
  | ⟨_, .inr (.inr ⟨_, r⟩)⟩ => !(decide (r.val.val % 2 = 1))

private def earlier (l : Label A) (v : Input m k) : Prop :=
  v.2 ∈ A v.1 ∧ rank A v / 2 < (l v.1).val

private def clauseBad (i : Fin m) (r : Nat) (v : Input m k) (b : Bool) : Prop :=
  v.1 = i ∧ v.2 ∈ A v.1 ∧
    ((rank A v = r ∧ b = false) ∨ (r % 2 = 1 ∧ rank A v + 1 = r ∧ b = true))

def bad : Aux A → Input m k → Bool → Prop
  | ⟨_, .inl _⟩, _, _ => False
  | ⟨l, .inr (.inl w)⟩, v, b => v = w ∧ earlier A l v ∧ b = true
  | ⟨_, .inr (.inr ⟨i, r⟩)⟩, v, b => clauseBad A i r.val.val v b

lemma bad_shore (u : Aux A) (v : Input m k) (b : Bool) (h : bad A u v b) :
    shore A u ≠ xor (col A v) b := by
  rcases u with ⟨l, z⟩
  rcases z with w | (w | ⟨i, r⟩)
  · exact False.elim h
  · change v = w ∧ earlier A l v ∧ b = true at h
    obtain ⟨hw, _, hb⟩ := h
    subst w
    subst b
    change col A v ≠ xor (col A v) true
    cases col A v <;> decide
  · change clauseBad A i r.val.val v b at h
    change (!(decide (r.val.val % 2 = 1))) ≠ xor (col A v) b
    rcases h.2.2 with ⟨hr, rfl⟩ | ⟨ho, ha, rfl⟩
    · simp only [col, hr]
      cases decide (r.val.val % 2 = 1) <;> decide
    · have he : rank A v % 2 ≠ 1 := by omega
      simp [ho, col, he]

variable (hcount : (∏ i, ((A i).card + 1) / 2) ≤ 2 ^ d)

def Eligible (x : Input m k → Bool) (b : Fin d → Bool) (u : Aux A) : Prop :=
  guard A hcount u = b ∧ ∀ v, ¬ bad A u v (x v)

def Saturated (x : Input m k → Bool) (b : Fin d → Bool) : Prop :=
  ∀ t, ∃ u, slot A u = t ∧ Eligible A hcount x b u

lemma slot_nonempty : Nonempty (Slot m k) := ⟨.inl ()⟩

private lemma input_eligible {x : Input m k → Bool} {b : Fin d → Bool} {l : Label A}
    {v : Input m k} : Eligible A hcount x b ⟨l, .inr (.inl v)⟩ ↔
      code A hcount l = b ∧ (earlier A l v → x v = false) := by
  change (code A hcount l = b ∧ ∀ w, ¬ (w = v ∧ earlier A l w ∧ x w = true)) ↔ _
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨h, fun he => ?_⟩
    cases hx : x v
    · rfl
    · exact (h' v ⟨rfl, he, hx⟩).elim
  · rintro ⟨h, h'⟩
    refine ⟨h, ?_⟩
    rintro w ⟨rfl, he, hx⟩
    simp [h' he] at hx

private lemma witness_hit {x : Input m k → Bool} {b : Fin d → Bool} {l : Label A}
    {i : Fin m} {r : PairRank A l i} (h : Eligible A hcount x b ⟨l, .inr (.inr ⟨i, r⟩)⟩) :
    x (point A i r.val) = true := by
  cases hx : x (point A i r.val)
  · exact (h.2 _ ⟨rfl, point_mem A i r.val, .inl ⟨rank_point A i r.val, hx⟩⟩).elim
  · rfl

private lemma witness_rank_eq {x : Input m k → Bool} {b : Fin d → Bool} {l : Label A}
    {i : Fin m} {r s : PairRank A l i}
    (hr : Eligible A hcount x b ⟨l, .inr (.inr ⟨i, r⟩)⟩)
    (hs : Eligible A hcount x b ⟨l, .inr (.inr ⟨i, s⟩)⟩) : r = s := by
  have hpair : r.val.val / 2 = s.val.val / 2 := r.property.trans s.property.symm
  have hnot (a c : PairRank A l i)
      (ha : Eligible A hcount x b ⟨l, .inr (.inr ⟨i, a⟩)⟩)
      (hc : Eligible A hcount x b ⟨l, .inr (.inr ⟨i, c⟩)⟩)
      (ho : c.val.val % 2 = 1) (hstep : a.val.val + 1 = c.val.val) : False :=
    hc.2 (point A i a.val) ⟨rfl, point_mem A i a.val,
      .inr ⟨ho, by rw [rank_point, hstep], witness_hit A hcount ha⟩⟩
  apply Subtype.ext
  apply Fin.ext
  by_contra hn
  have hor : (r.val.val + 1 = s.val.val ∧ s.val.val % 2 = 1) ∨
      (s.val.val + 1 = r.val.val ∧ r.val.val % 2 = 1) := by omega
  rcases hor with ⟨ha, ho⟩ | ⟨ha, ho⟩
  · exact hnot r s hr hs ho ha
  · exact hnot s r hs hr ho ha

lemma unique {x : Input m k → Bool} {b : Fin d → Bool} {u v : Aux A}
    (hu : Eligible A hcount x b u) (hv : Eligible A hcount x b v)
    (ht : slot A u = slot A v) : u = v := by
  rcases u with ⟨l, z⟩
  rcases v with ⟨l', z'⟩
  have hl : l = l' := code_injective A hcount (hu.1.trans hv.1.symm)
  subst l'
  rcases z with u | (v | ⟨i, r⟩) <;> rcases z' with u' | (v' | ⟨i', s⟩) <;>
    simp only [slot, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at ht
  · cases u; cases u'; rfl
  · subst v'; rfl
  · subst i'
    rw [witness_rank_eq A hcount hu hv]

private lemma saturated_code {x : Input m k → Bool} {b : Fin d → Bool}
    (h : Saturated A hcount x b) : ∃ l, code A hcount l = b := by
  obtain ⟨⟨l, z⟩, _, he⟩ := h (.inl ())
  exact ⟨l, he.1⟩

private lemma saturated_input {x : Input m k → Bool} {b : Fin d → Bool} {l : Label A}
    (h : Saturated A hcount x b) (hb : code A hcount l = b)
    (v : Input m k) (he : earlier A l v) : x v = false := by
  obtain ⟨⟨l', z⟩, ht, hu⟩ := h (.inr (.inl v))
  have hl : l' = l := code_injective A hcount (hu.1.trans hb.symm)
  subst l'
  rcases z with u | (w | ⟨i, r⟩) <;>
    simp only [slot, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at ht
  subst w
  exact ((input_eligible A hcount).mp hu).2 he

private lemma saturated_row {x : Input m k → Bool} {b : Fin d → Bool} {l : Label A}
    (h : Saturated A hcount x b) (hb : code A hcount l = b) (i : Fin m) :
    ∃ r : PairRank A l i, x (point A i r.val) = true := by
  obtain ⟨⟨l', z⟩, ht, hu⟩ := h (.inr (.inr i))
  have hl : l' = l := code_injective A hcount (hu.1.trans hb.symm)
  subst l'
  rcases z with u | (w | ⟨j, r⟩) <;>
    simp only [slot, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at ht
  subst j
  exact ⟨r, witness_hit A hcount hu⟩

lemma saturated_guard_unique {x : Input m k → Bool} {b b' : Fin d → Bool}
    (h : Saturated A hcount x b) (h' : Saturated A hcount x b') : b = b' := by
  obtain ⟨l, hl⟩ := saturated_code A hcount h
  obtain ⟨l', hl'⟩ := saturated_code A hcount h'
  have hle (a c : Label A) (ba bc : Fin d → Bool)
      (ha : Saturated A hcount x ba) (hc : Saturated A hcount x bc)
      (hba : code A hcount a = ba) (hbc : code A hcount c = bc) (i : Fin m) :
      (c i).val ≤ (a i).val := by
    obtain ⟨r, hr⟩ := saturated_row A hcount ha hba i
    by_contra! hlt
    have he : earlier A c (point A i r.val) := by
      refine ⟨point_mem A i r.val, ?_⟩
      rwa [rank_point, r.property]
    have hf := saturated_input A hcount hc hbc _ he
    simp [hr] at hf
  have he : l = l' := by
    funext i
    apply Fin.ext
    exact Nat.le_antisymm (hle l' l b' b h' h hl' hl i) (hle l l' b b' h h' hl hl' i)
  exact hl.symm.trans ((congrArg (code A hcount) he).trans hl')

lemma covered_of_saturated {x : Input m k → Bool} {b : Fin d → Bool}
    (h : Saturated A hcount x b) : ∀ i, ∃ j ∈ A i, x (i, j) = true := by
  obtain ⟨l, hl⟩ := saturated_code A hcount h
  intro i
  obtain ⟨r, hr⟩ := saturated_row A hcount h hl i
  exact ⟨(point A i r.val).2, point_mem A i r.val, hr⟩

lemma saturated_of_covered {x : Input m k → Bool}
    (hx : ∀ i, ∃ j ∈ A i, x (i, j) = true) : ∃ b, Saturated A hcount x b := by
  have hex (i : Fin m) : ∃ r : Fin (A i).card, x (point A i r) = true := by
    obtain ⟨j, hj, ht⟩ := hx i
    refine ⟨(A i).equivFin ⟨j, hj⟩, ?_⟩
    simpa [point] using ht
  let r (i : Fin m) : Fin (A i).card := Fin.find (fun q => x (point A i q) = true) (hex i)
  have hr (i : Fin m) : x (point A i (r i)) = true := Fin.find_spec (hex i)
  have hmin (v : Input m k) (hv : v.2 ∈ A v.1) (hlt : rank A v < (r v.1).val) :
      x v ≠ true := by
    have hq : (A v.1).equivFin ⟨v.2, hv⟩ < r v.1 := by
      change ((A v.1).equivFin ⟨v.2, hv⟩).val < (r v.1).val
      rwa [← rank_eq_of_mem A v hv]
    have hn := Fin.find_min (hex v.1) hq
    simpa only [point_rank A v hv] using hn
  let l : Label A := fun i => ⟨(r i).val / 2, by have hi := (r i).isLt; omega⟩
  refine ⟨code A hcount l, ?_⟩
  rintro (u | (v | i))
  · exact ⟨⟨l, .inl ()⟩, by cases u; rfl, rfl, fun _ => id⟩
  · refine ⟨⟨l, .inr (.inl v)⟩, rfl, (input_eligible A hcount).mpr ⟨rfl, ?_⟩⟩
    rintro ⟨hv, he⟩
    change rank A v / 2 < (r v.1).val / 2 at he
    have hn := hmin v hv (by omega)
    cases heq : x v
    · rfl
    · exact (hn heq).elim
  · refine ⟨⟨l, .inr (.inr ⟨i, ⟨r i, rfl⟩⟩)⟩, rfl, rfl, ?_⟩
    rintro ⟨a, j⟩ hv
    change clauseBad A i (r i).val (a, j) (x (a, j)) at hv
    rcases hv with ⟨hai, hj, hbad⟩
    change a = i at hai
    subst a
    rcases hbad with ⟨he, hf⟩ | ⟨_, he, ht⟩
    · have he' : (A i).equivFin ⟨j, hj⟩ = r i := by
        apply Fin.ext
        exact (rank_eq_of_mem A (i, j) hj).symm.trans he
      have hp := point_rank A (i, j) hj
      rw [he'] at hp
      have hhit := hr i
      rw [hp] at hhit
      simp [hhit] at hf
    · exact hmin (i, j) hj (by change rank A (i, j) < (r i).val; omega) ht

lemma saturated_iff (x : Input m k → Bool) :
    (∃! b, Saturated A hcount x b) ↔ ∀ i, ∃ j ∈ A i, x (i,j) = true := by
  constructor
  · rintro ⟨b, hb, _⟩
    exact covered_of_saturated A hcount hb
  · intro hx
    obtain ⟨b, hb⟩ := saturated_of_covered A hcount hx
    exact ⟨b, hb, fun _ hb' => saturated_guard_unique A hcount hb' hb⟩

lemma saturated_example (hne : ∀ i, (A i).Nonempty) :
    ∃ (x : Input m k → Bool) (b : Fin d → Bool), Saturated A hcount x b := by
  refine ⟨fun _ => true, saturated_of_covered A hcount ?_⟩
  intro i
  obtain ⟨j, hj⟩ := hne i
  exact ⟨j, hj, rfl⟩

end PairPartition

namespace GuardedGraph

open scoped BigOperators Classical

variable {V U T : Type*} {d : Nat}

abbrev Vertex (V : Type*) (d : Nat) (U : Type*) :=
  (V × Bool) ⊕ ((Fin d × Option Bool) ⊕ U)

abbrev input (v : V) (q : Bool) : Vertex V d U := .inl (v, q)
abbrev bit (i : Fin d) (o : Option Bool) : Vertex V d U := .inr (.inl (i, o))
abbrev aux (u : U) : Vertex V d U := .inr (.inr u)

def IsCenter : Vertex V d U → Prop
  | .inr (.inl (_, none)) => True
  | _ => False

def Shore (col : V → Bool) (shore : U → Bool) : Vertex V d U → Bool
  | .inl (v, q) => xor (col v) q
  | .inr (.inl (_, none)) => false
  | .inr (.inl (_, some q)) => q
  | .inr (.inr u) => shore u

/-- A false label bit takes the center; a true bit takes both leaves. -/
def Edge (guard : U → Fin d → Bool) (shore : U → Bool)
    (bad : U → V → Bool → Prop) (a z : Vertex V d U) : Prop :=
  (∃ v : V, a = input v false ∧ z = input v true) ∨
  (∃ (i : Fin d) (q : Bool), a = bit i none ∧ z = bit i (some q)) ∨
  (∃ (u : U) (i : Fin d), a = aux u ∧ z = bit i none ∧ guard u i = true) ∨
  (∃ (u : U) (i : Fin d), a = aux u ∧ z = bit i (some (!shore u)) ∧ guard u i = false) ∨
  (∃ (u : U) (v : V) (q : Bool), a = aux u ∧ z = input v q ∧ bad u v q)

variable {guard : U → Fin d → Bool} {shore : U → Bool} {bad : U → V → Bool → Prop}
variable {slot : U → T}

namespace Edge

theorem inputPair (v : V) : Edge guard shore bad (input v false) (input v true) :=
  Or.inl ⟨v, rfl, rfl⟩

theorem centerLeaf (i : Fin d) (q : Bool) : Edge guard shore bad (bit i none) (bit i (some q)) :=
  Or.inr (Or.inl ⟨i, q, rfl, rfl⟩)

theorem guardCenter (u : U) (i : Fin d) (h : guard u i = true) :
    Edge guard shore bad (aux u) (bit i none) :=
  Or.inr (Or.inr (Or.inl ⟨u, i, rfl, rfl, h⟩))

theorem guardLeaf (u : U) (i : Fin d) (h : guard u i = false) :
    Edge guard shore bad (aux u) (bit i (some (!shore u))) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨u, i, rfl, rfl, h⟩)))

theorem badInput (u : U) (v : V) (q : Bool) (h : bad u v q) :
    Edge guard shore bad (aux u) (input v q) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨u, v, q, rfl, rfl, h⟩)))

end Edge

theorem edge_ne {a z : Vertex V d U} (he : Edge guard shore bad a z) : a ≠ z := by
  unfold Edge at he
  rcases he with ⟨v, rfl, rfl⟩ | ⟨i, q, rfl, rfl⟩ | ⟨u, i, rfl, rfl, h⟩ |
    ⟨u, i, rfl, rfl, h⟩ | ⟨u, v, q, rfl, rfl, h⟩ <;> simp

theorem edge_irrefl (a : Vertex V d U) : ¬ Edge guard shore bad a a :=
  fun h => edge_ne h rfl

theorem edge_cross (col : V → Bool)
    (hbad : ∀ u v q, bad u v q → shore u ≠ xor (col v) q)
    {a z : Vertex V d U} (he : Edge guard shore bad a z)
    (ha : ¬ IsCenter a) (hz : ¬ IsCenter z) : Shore col shore a ≠ Shore col shore z := by
  unfold Edge at he
  rcases he with ⟨v, rfl, rfl⟩ | ⟨i, q, rfl, rfl⟩ | ⟨u, i, rfl, rfl, h⟩ |
    ⟨u, i, rfl, rfl, h⟩ | ⟨u, v, q, rfl, rfl, h⟩
  · cases hc : col v <;> simp [Shore, hc]
  · exact False.elim (ha trivial)
  · exact False.elim (hz trivial)
  · cases hs : shore u <;> simp [Shore, hs]
  · exact hbad u v q h

def Independent (guard : U → Fin d → Bool) (shore : U → Bool)
    (bad : U → V → Bool → Prop) (I : Vertex V d U → Prop) : Prop :=
  ∀ ⦃a z⦄, Edge guard shore bad a z → I a → I z → False

def Eligible (guard : U → Fin d → Bool) (bad : U → V → Bool → Prop)
    (x : V → Bool) (b : Fin d → Bool) (u : U) : Prop :=
  guard u = b ∧ ∀ v, ¬ bad u v (x v)

def SlotUnique (slot : U → T) (guard : U → Fin d → Bool)
    (bad : U → V → Bool → Prop) : Prop :=
  ∀ ⦃x b u w⦄, Eligible guard bad x b u → Eligible guard bad x b w → slot u = slot w → u = w

def Saturated (slot : U → T) (guard : U → Fin d → Bool)
    (bad : U → V → Bool → Prop) (x : V → Bool) (b : Fin d → Bool) : Prop :=
  ∀ t, ∃ u, Eligible guard bad x b u ∧ slot u = t

def Core (I : Vertex V d U → Prop) (x : V → Bool) (b : Fin d → Bool) : Prop :=
  (∀ v q, I (input v q) ↔ q = x v) ∧
  (∀ i, I (bit i none) ↔ b i = false) ∧
  (∀ i q, I (bit i (some q)) ↔ b i = true)

def Realize (guard : U → Fin d → Bool) (bad : U → V → Bool → Prop)
    (x : V → Bool) (b : Fin d → Bool) : Vertex V d U → Prop
  | .inl (v, q) => q = x v
  | .inr (.inl (i, none)) => b i = false
  | .inr (.inl (i, some _)) => b i = true
  | .inr (.inr u) => Eligible guard bad x b u

theorem core_realize (x : V → Bool) (b : Fin d → Bool) :
    Core (Realize guard bad x b) x b :=
  ⟨fun _ _ => Iff.rfl, fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩

theorem core_unique {I : Vertex V d U → Prop} {x y : V → Bool} {b c : Fin d → Bool}
    (hx : Core I x b) (hy : Core I y c) : x = y ∧ b = c := by
  constructor
  · funext v
    exact (hy.1 v (x v)).1 ((hx.1 v (x v)).2 rfl)
  · funext i
    cases hb : b i <;> cases hc : c i
    · rfl
    · have h := (hy.2.1 i).1 ((hx.2.1 i).2 hb)
      simp [hc] at h
    · have h := (hx.2.1 i).1 ((hy.2.1 i).2 hc)
      simp [hb] at h
    · rfl

theorem realize_independent (x : V → Bool) (b : Fin d → Bool) :
    Independent guard shore bad (Realize guard bad x b) := by
  intro a z e
  unfold Edge at e
  rcases e with ⟨v, rfl, rfl⟩ | ⟨i, q, rfl, rfl⟩ | ⟨u, i, rfl, rfl, h⟩ |
    ⟨u, i, rfl, rfl, h⟩ | ⟨u, v, q, rfl, rfl, h⟩
  · intro hf ht
    change false = x v at hf
    change true = x v at ht
    exact Bool.false_ne_true (hf.trans ht.symm)
  · intro hf ht
    change b i = false at hf
    change b i = true at ht
    exact Bool.false_ne_true (hf.symm.trans ht)
  · intro hu hc
    change Eligible guard bad x b u at hu
    change b i = false at hc
    have hh := congrFun hu.1 i
    simp [h, hc] at hh
  · intro hu hl
    change Eligible guard bad x b u at hu
    change b i = true at hl
    have hh := congrFun hu.1 i
    simp [h, hl] at hh
  · intro hu hq
    change Eligible guard bad x b u at hu
    change q = x v at hq
    exact hu.2 v (hq ▸ h)

theorem eligible_of_mem {I : Vertex V d U → Prop} (hI : Independent guard shore bad I)
    {x : V → Bool} {b : Fin d → Bool} (hc : Core I x b) {u : U} (hu : I (aux u)) :
    Eligible guard bad x b u := by
  constructor
  · funext i
    cases hg : guard u i <;> cases hb : b i
    · rfl
    · exact False.elim (hI (Edge.guardLeaf u i hg) hu ((hc.2.2 i _).2 hb))
    · exact False.elim (hI (Edge.guardCenter u i hg) hu ((hc.2.1 i).2 hb))
    · rfl
  · intro v hv
    exact hI (Edge.badInput u v (x v) hv) hu ((hc.1 v (x v)).2 rfl)

private def heavy (U : Type*) [Fintype U] : Nat := Fintype.card U + 1

def weight [Fintype U] : Vertex V d U → Nat
  | .inl _ => heavy U
  | .inr (.inl (_, none)) => heavy U * 2
  | .inr (.inl (_, some _)) => heavy U
  | .inr (.inr _) => 1

theorem weight_pos [Fintype U] (z : Vertex V d U) : 0 < weight z := by
  rcases z with z | z
  · simp [weight, heavy]
  rcases z with ⟨i, o⟩ | u
  · cases o <;> simp [weight, heavy]
  · exact Nat.zero_lt_one

noncomputable def total [Fintype V] [Fintype U] (I : Vertex V d U → Prop) : Nat :=
  ∑ z, if I z then weight z else 0

def Maximum [Fintype V] [Fintype U] (guard : U → Fin d → Bool) (shore : U → Bool)
    (bad : U → V → Bool → Prop) (I : Vertex V d U → Prop) : Prop :=
  Independent guard shore bad I ∧ ∀ J, Independent guard shore bad J → total J ≤ total I

private noncomputable def auxSet [Fintype U] (I : Vertex V d U → Prop) : Finset U :=
  Finset.univ.filter (fun u => I (aux u))

private noncomputable def coreCount (I : Vertex V d U → Prop) : V ⊕ Fin d → Nat
  | .inl v => (if I (input v true) then 1 else 0) + (if I (input v false) then 1 else 0)
  | .inr i => (if I (bit i none) then 2 else 0) +
      ((if I (bit i (some true)) then 1 else 0) + (if I (bit i (some false)) then 1 else 0))

private def capacity : V ⊕ Fin d → Nat
  | .inl _ => 1
  | .inr _ => 2

private def coreLimit (V U : Type*) (d : Nat) [Fintype V] [Fintype U] : Nat :=
  heavy U * ∑ j : V ⊕ Fin d, capacity j

def ceiling (V U T : Type*) (d : Nat) [Fintype V] [Fintype U] [Fintype T] : Nat :=
  coreLimit V U d + Fintype.card T

private theorem total_eq [Fintype V] [Fintype U] (I : Vertex V d U → Prop) :
    total I = heavy U * (∑ j, coreCount I j) + (auxSet I).card := by
  have hin : (∑ v : V, ∑ q : Bool, if I (input v q) then weight (input (d := d) (U := U) v q) else 0) =
      ∑ v : V, heavy U * coreCount I (.inl v) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [Fintype.sum_bool]
    by_cases ht : I (input v true) <;> by_cases hf : I (input v false) <;>
      simp [coreCount, weight, ht, hf, Nat.mul_two]
  have hbit : (∑ i : Fin d, ∑ q : Option Bool, if I (bit i q) then weight (bit (V := V) (U := U) i q) else 0) =
      ∑ i : Fin d, heavy U * coreCount I (.inr i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Fintype.sum_option, Fintype.sum_bool]
    by_cases hn : I (bit i none) <;> by_cases ht : I (bit i (some true)) <;>
      by_cases hf : I (bit i (some false)) <;>
      simp [coreCount, weight, hn, ht, hf, Nat.mul_add, Nat.mul_succ, Nat.add_assoc]
  have haux : (∑ u : U, if I (aux u) then weight (aux (V := V) (d := d) u) else 0) = (auxSet I).card :=
    Finset.sum_boole _ _
  unfold total
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  rw [hin, hbit, haux]
  simp only [Fintype.sum_sum_type, Nat.mul_add, Finset.mul_sum, Nat.add_assoc]

private theorem count_le {I : Vertex V d U → Prop} (hI : Independent guard shore bad I)
    (j : V ⊕ Fin d) : coreCount I j ≤ capacity j := by
  rcases j with v | i
  · by_cases ht : I (input v true)
    · have hf : ¬ I (input v false) := fun h => hI (Edge.inputPair v) h ht
      simp [coreCount, capacity, ht, hf]
    · by_cases hf : I (input v false) <;> simp [coreCount, capacity, ht, hf]
  · by_cases hn : I (bit i none)
    · have hl (q : Bool) : ¬ I (bit i (some q)) := fun h => hI (Edge.centerLeaf i q) hn h
      simp [coreCount, capacity, hn, hl]
    · by_cases ht : I (bit i (some true)) <;> by_cases hf : I (bit i (some false)) <;>
        simp [coreCount, capacity, hn, ht, hf]

private theorem full_count [Fintype V] {I : Vertex V d U → Prop}
    {x : V → Bool} {b : Fin d → Bool} (hc : Core I x b) :
    (∑ j, coreCount I j) = ∑ j : V ⊕ Fin d, capacity j := by
  apply Finset.sum_congr rfl
  intro j _
  rcases j with v | i
  · cases h : x v <;> simp [coreCount, capacity, hc.1, h]
  · cases h : b i <;> simp [coreCount, capacity, hc.2.1, hc.2.2, h]

private theorem core_of_full [Fintype V] {I : Vertex V d U → Prop}
    (hI : Independent guard shore bad I) (hfull : (∑ j, coreCount I j) = ∑ j : V ⊕ Fin d, capacity j) :
    ∃ x b, Core I x b := by
  have hall := (Finset.sum_eq_sum_iff_of_le (fun j _ => count_le hI j)).1 hfull
  let x : V → Bool := fun v => if I (input v true) then true else false
  let b : Fin d → Bool := fun i => if I (bit i none) then false else true
  refine ⟨x, b, ?_, ?_, ?_⟩
  · intro v q
    by_cases ht : I (input v true)
    · have hf : ¬ I (input v false) := fun h => hI (Edge.inputPair v) h ht
      cases q <;> simp [x, ht, hf]
    · have he := hall (.inl v) (Finset.mem_univ _)
      have hf : I (input v false) := by
        by_contra h
        simp [coreCount, capacity, ht, h] at he
      cases q <;> simp [x, ht, hf]
  · intro i
    by_cases hn : I (bit i none) <;> simp [b, hn]
  · intro i q
    by_cases hn : I (bit i none)
    · have hl : ¬ I (bit i (some q)) := fun h => hI (Edge.centerLeaf i q) hn h
      simp [b, hn, hl]
    · have he := hall (.inr i) (Finset.mem_univ _)
      have hh : I (bit i (some true)) ∧ I (bit i (some false)) := by
        by_cases ht : I (bit i (some true)) <;> by_cases hf : I (bit i (some false)) <;>
          simp [coreCount, capacity, hn, ht, hf] at he ⊢
      cases q <;> simp [b, hn, hh.1, hh.2]

private theorem core_or_low [Fintype V] [Fintype U] {I : Vertex V d U → Prop}
    (hI : Independent guard shore bad I) :
    (∃ x b, Core I x b) ∨ total I < coreLimit V U d := by
  have hle : (∑ j, coreCount I j) ≤ ∑ j : V ⊕ Fin d, capacity j :=
    Finset.sum_le_sum fun j _ => count_le hI j
  rcases eq_or_lt_of_le hle with he | hl
  · exact Or.inl (core_of_full hI he)
  · right
    have hstep := Nat.mul_le_mul_left (heavy U) (Nat.succ_le_of_lt hl)
    have haux : (auxSet I).card < heavy U :=
      Nat.lt_succ_of_le (Finset.card_le_card (Finset.subset_univ (auxSet I)))
    rw [Nat.mul_succ] at hstep
    rw [total_eq, coreLimit]
    omega

private theorem aux_slot_inj [Fintype U] (hu : SlotUnique slot guard bad)
    {I : Vertex V d U → Prop} (hI : Independent guard shore bad I)
    {x : V → Bool} {b : Fin d → Bool} (hc : Core I x b) :
    Set.InjOn slot (auxSet I : Set U) := by
  intro u huI w hwI h
  exact hu (eligible_of_mem hI hc (Finset.mem_filter.mp huI).2)
    (eligible_of_mem hI hc (Finset.mem_filter.mp hwI).2) h

private theorem aux_card_le [Fintype U] [Fintype T] (hu : SlotUnique slot guard bad)
    {I : Vertex V d U → Prop} (hI : Independent guard shore bad I)
    {x : V → Bool} {b : Fin d → Bool} (hc : Core I x b) : (auxSet I).card ≤ Fintype.card T := by
  rw [← Finset.card_image_of_injOn (aux_slot_inj hu hI hc)]
  exact Finset.card_le_card (Finset.subset_univ _)

theorem total_le_ceiling [Fintype V] [Fintype U] [Fintype T] (hu : SlotUnique slot guard bad)
    {I : Vertex V d U → Prop} (hI : Independent guard shore bad I) :
    total I ≤ ceiling V U T d := by
  rcases core_or_low hI with ⟨x, b, hc⟩ | hl
  · rw [total_eq, full_count hc, ceiling, coreLimit]
    exact Nat.add_le_add_left (aux_card_le hu hI hc) _
  · exact hl.le.trans (Nat.le_add_right _ _)

theorem total_realize [Fintype V] [Fintype U] [Fintype T] (hu : SlotUnique slot guard bad)
    {x : V → Bool} {b : Fin d → Bool} (hs : Saturated slot guard bad x b) :
    total (Realize guard bad x b) = ceiling V U T d := by
  let I := Realize guard bad x b
  have hc : Core I x b := core_realize x b
  have hinj : Set.InjOn slot (auxSet I : Set U) := by
    intro u h₁ w h₂ he
    exact hu (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2 he
  have himg : (auxSet I).image slot = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro t
    obtain ⟨u, he, ht⟩ := hs t
    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, ht⟩
  have hcard : (auxSet I).card = Fintype.card T := by
    rw [← Finset.card_image_of_injOn hinj, himg, Finset.card_univ]
  change total I = _
  rw [total_eq, full_count hc, hcard, ceiling, coreLimit]

theorem maximum_realize [Fintype V] [Fintype U] [Fintype T] (hu : SlotUnique slot guard bad)
    {x : V → Bool} {b : Fin d → Bool} (hs : Saturated slot guard bad x b) :
    Maximum guard shore bad (Realize guard bad x b) := by
  refine ⟨realize_independent x b, ?_⟩
  intro J hJ
  rw [total_realize hu hs]
  exact total_le_ceiling hu hJ

theorem maximum_iff [Fintype V] [Fintype U] [Fintype T] (hu : SlotUnique slot guard bad)
    (hex : ∃ x b, Saturated slot guard bad x b) {I : Vertex V d U → Prop} :
    Maximum guard shore bad I ↔ ∃ x b, Saturated slot guard bad x b ∧ I = Realize guard bad x b := by
  constructor
  · rintro ⟨hI, hm⟩
    have htot : total I = ceiling V U T d := by
      apply le_antisymm (total_le_ceiling hu hI)
      obtain ⟨x, b, hs⟩ := hex
      rw [← total_realize hu hs]
      exact hm _ (realize_independent x b)
    obtain ⟨x, b, hc⟩ : ∃ x b, Core I x b := by
      rcases core_or_low hI with h | hl
      · exact h
      · rw [htot, ceiling] at hl
        omega
    have hcard : (auxSet I).card = Fintype.card T := by
      rw [total_eq, full_count hc, ceiling, coreLimit] at htot
      exact Nat.add_left_cancel htot
    have himg : (auxSet I).image slot = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_image_of_injOn (aux_slot_inj hu hI hc), hcard, Finset.card_univ]
    have hsI (t : T) : ∃ u, I (aux u) ∧ slot u = t := by
      have ht : t ∈ (auxSet I).image slot := by rw [himg]; exact Finset.mem_univ _
      obtain ⟨u, huI, huT⟩ := Finset.mem_image.mp ht
      exact ⟨u, (Finset.mem_filter.mp huI).2, huT⟩
    refine ⟨x, b, ?_, ?_⟩
    · intro t
      obtain ⟨u, huI, ht⟩ := hsI t
      exact ⟨u, eligible_of_mem hI hc huI, ht⟩
    · funext z
      apply propext
      rcases z with ⟨v, q⟩ | z
      · exact hc.1 v q
      rcases z with ⟨i, o⟩ | u
      · cases o with
        | none => exact hc.2.1 i
        | some q => exact hc.2.2 i q
      · change I (aux u) ↔ Eligible guard bad x b u
        refine ⟨eligible_of_mem hI hc, fun he => ?_⟩
        obtain ⟨w, hwI, hws⟩ := hsI (slot u)
        have heq := hu (eligible_of_mem hI hc hwI) he hws
        exact heq ▸ hwI
  · rintro ⟨x, b, hs, rfl⟩
    exact maximum_realize hu hs

/-- A fixed core of a maximum determines the entire independent set. -/
theorem maximum_unique [Fintype V] [Fintype U] [Fintype T] (hu : SlotUnique slot guard bad)
    {x : V → Bool} {b : Fin d → Bool} (hs : Saturated slot guard bad x b)
    {I : Vertex V d U → Prop} (hm : Maximum guard shore bad I) (hc : Core I x b) :
    I = Realize guard bad x b := by
  obtain ⟨y, c, _, he⟩ := (maximum_iff hu ⟨x, b, hs⟩).1 hm
  have hy : Core I y c := he.symm ▸ core_realize y c
  obtain ⟨rfl, rfl⟩ := core_unique hc hy
  exact he

end GuardedGraph


private lemma upper {m k d : Nat} (A : Fin m → Finset (Fin k))
    (hA : ∀ i, (A i).Nonempty) (hcount : (∏ i, ((A i).card+1)/2) ≤ 2^d) :
    ∃ (N : Nat) (G : Finset (Fin N × Fin N)) (w : Fin N → Nat)
      (p : Fin m × Fin k → Fin N) (D S : Finset (Fin N)), D.card ≤ d ∧ shores G D S ∧
      (∀ e ∈ G, e.1 < e.2) ∧
      (∀ X, hits A X ↔ ∃ C, minimum G w C ∧ projection p C = X) ∧
      Function.Injective p ∧ (∀ v, 0 < w v) ∧
      ∀ B C, minimum G w B → minimum G w C → projection p B = projection p C → B = C := by
  let V := Fin m × Fin k
  let Q := PairPartition.Aux A
  let U := GuardedGraph.Vertex V d Q
  let guard := PairPartition.guard A hcount
  let shore := PairPartition.shore A
  let bad := PairPartition.bad A
  let slot := PairPartition.slot A
  let E : U → U → Prop := GuardedGraph.Edge guard shore bad
  let w : U → Nat := GuardedGraph.weight
  let port : V ↪ U := ⟨fun v => GuardedGraph.input v false, by
    intro v v' h
    exact congrArg Prod.fst (Sum.inl.inj h)⟩
  let del : Fin d ↪ U := ⟨fun i => GuardedGraph.bit i none, by
    intro i j h
    exact congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj h))⟩
  let color : U → Bool := GuardedGraph.Shore (PairPartition.col A) shore
  let Sat := PairPartition.Saturated A hcount
  have hSat (x : V → Bool) (b : Fin d → Bool) :
      Sat x b ↔ GuardedGraph.Saturated slot guard bad x b := by
    constructor <;> intro h t <;>
      obtain ⟨u, h₁, h₂⟩ := h t <;> exact ⟨u, h₂, h₁⟩
  have hu : GuardedGraph.SlotUnique slot guard bad := by
    intro x b u v hu hv he
    exact PairPartition.unique A hcount hu hv he
  have hex : ∃ x b, GuardedGraph.Saturated slot guard bad x b := by
    obtain ⟨x, b, h⟩ := PairPartition.saturated_example A hcount hA
    exact ⟨x, b, (hSat x b).1 h⟩
  have hm := realization E w port (hits A) Sat (GuardedGraph.Realize guard bad)
    (fun _ _ _ => eq_comm) (by
      intro X
      rw [PairPartition.saturated_iff]
      simp [hits]) (fun _ _ _ h h' => PairPartition.saturated_guard_unique A hcount h h') (by
      intro I
      change GuardedGraph.Maximum guard shore bad I ↔ _
      rw [GuardedGraph.maximum_iff hu hex]
      constructor
      · rintro ⟨x, b, h, rfl⟩
        exact ⟨x, b, (hSat x b).2 h, rfl⟩
      · rintro ⟨x, b, h, rfl⟩
        exact ⟨x, b, (hSat x b).1 h, rfl⟩)
  refine transport d E w port del color (hits A) (GuardedGraph.edge_irrefl) ?_
    GuardedGraph.weight_pos hm.1 hm.2
  intro u v he hu hv
  apply GuardedGraph.edge_cross _ (PairPartition.bad_shore A) he
  · intro hc
    rcases u with _ | (⟨i, o⟩ | _)
    · exact hc
    · cases o
      · exact hu i rfl
      · exact hc
    · exact hc
  · intro hc
    rcases v with _ | (⟨i, o⟩ | _)
    · exact hc
    · cases o
      · exact hv i rfl
      · exact hc
    · exact hc


end PEqualNP.Outside.L_lib_1509_aux

open PEqualNP.Outside.L_lib_1509_aux

theorem PEqualNP.Outside.L_lib_1509 :
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    let cover := fun {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) =>
      ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
    let opt := fun {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (C : Finset (Fin N)) =>
      cover G C ∧ ∀ B, cover G B → C.sum w ≤ B.sum w
    let bip := fun {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) =>
      ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
    let view := fun {k N : Nat} (p : Fin k → Fin N) (C : Finset (Fin N)) =>
      Finset.univ.filter (fun i => p i ∈ C)
    ∀ (m k d : Nat) (A : Fin m → Finset (Fin k)), (∀ i, (A i).Nonempty) →
    let V := Fin m × Fin k
    let target := fun (X : Finset V) => ∀ i, ∃ j ∈ A i, (i,j) ∈ X
    let sig := fun {N : Nat} (p : V → Fin N) (C : Finset (Fin N)) =>
      Finset.univ.filter (fun i : V => p i ∈ C)
    let host := fun (one : Bool) => ∃ (N : Nat) (G : Finset (Fin N × Fin N)) (w : Fin N → Nat)
      (p : V → Fin N) (D S : Finset (Fin N)), D.card ≤ d ∧ bip G D S ∧ (∀ e ∈ G, e.1<e.2) ∧
      (∀ X, target X ↔ ∃ C, opt G w C ∧ sig p C=X) ∧
      (one=true → Function.Injective p ∧ (∀ v, 0<w v) ∧
        ∀ B C, opt G w B → opt G w C → sig p B=sig p C → B=C)
    let count := Finset.univ.prod (fun i => ((A i).card+1)/2)
    (host false ↔ count ≤ 2^d) ∧ (count ≤ 2^d → host true) := by
  dsimp only
  intro m k d A hA
  constructor
  · constructor
    · rintro ⟨N, G, w, p, D, S, hd, hs, _, hmodels, _⟩
      exact lower A G w p D S hd hs hmodels
    · intro h
      obtain ⟨N, G, w, p, D, S, hd, hs, ho, hm, _⟩ := upper A hA h
      exact ⟨N, G, w, p, D, S, hd, hs, ho, hm, fun hfalse => Bool.noConfusion hfalse⟩
  · intro h
    obtain ⟨N, G, w, p, D, S, hd, hs, ho, hm, huniq⟩ := upper A hA h
    exact ⟨N, G, w, p, D, S, hd, hs, ho, hm, fun _ => huniq⟩

