import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1516

open Finset

section Comb

private def missing {d t : Nat} (X : Finset (Fin (2 ^ d) × (Fin t × Bool))) (z : Fin (2 ^ d)) :
    Finset (Fin t) :=
  Finset.univ.filter (fun i : Fin t => (z, i, false) ∉ X ∧ (z, i, true) ∉ X)

private def mkClause {d t : Nat} (F : Fin (2 ^ d) → Finset (Fin t)) :
    Finset (Fin (2 ^ d) × (Fin t × Bool)) :=
  Finset.univ.filter (fun v : Fin (2 ^ d) × (Fin t × Bool) => v.2.1 ∈ F v.1)

private lemma mkClause_inj {d t : Nat} :
    Function.Injective (@mkClause d t) := by
  intro F1 F2 h
  funext z
  ext i
  have hmem : (z, i, false) ∈ mkClause F1 ↔ (z, i, false) ∈ mkClause F2 := by rw [h]
  simpa [mkClause] using hmem

private lemma mkClause_card {d t r : Nat} {F : Fin (2 ^ d) → Finset (Fin t)}
    (hF : ∀ z, (F z).card = r + 1) :
    (mkClause F).card = 2 * (r + 1) * 2 ^ d := by
  classical
  have heq : mkClause F =
      (Finset.univ : Finset (Fin (2 ^ d))).biUnion
        (fun z => (F z).biUnion (fun i => {(z, i, false), (z, i, true)})) := by
    ext ⟨z, i, b⟩
    simp only [mkClause, mem_filter, mem_univ, true_and, mem_biUnion, mem_insert, mem_singleton,
      Prod.mk.injEq]
    constructor
    · intro hi
      refine ⟨z, i, hi, ?_⟩
      cases b <;> simp
    · rintro ⟨z', i', hi', h1 | h2⟩
      · rcases h1 with ⟨rfl, rfl, _⟩; exact hi'
      · rcases h2 with ⟨rfl, rfl, _⟩; exact hi'
  rw [heq, card_biUnion]
  · have hinner : ∀ z : Fin (2 ^ d),
        ((F z).biUnion (fun i => {(z, i, false), (z, i, true)})).card = 2 * (r + 1) := by
      intro z
      rw [card_biUnion]
      · have hpair : ∀ i ∈ F z, ({(z, i, false), (z, i, true)} :
            Finset (Fin (2 ^ d) × (Fin t × Bool))).card = 2 := by
          intro i _
          rw [card_pair]
          simp
        rw [sum_congr rfl hpair, sum_const, hF z, smul_eq_mul, Nat.mul_comm]
      · intro i1 _ i2 _ hne
        dsimp only [Function.onFun]
        rw [disjoint_left]
        intro x hx1 hx2
        simp only [mem_insert, mem_singleton] at hx1 hx2
        rcases hx1 with rfl | rfl <;> rcases hx2 with h | h <;> simp at h <;> exact hne h
    rw [sum_congr rfl (fun z _ => hinner z), sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_comm]
  · intro z1 _ z2 _ hne
    dsimp only [Function.onFun]
    rw [disjoint_left]
    intro x hx1 hx2
    simp only [mem_biUnion, mem_insert, mem_singleton] at hx1 hx2
    obtain ⟨i1, _, h1 | h1⟩ := hx1 <;> obtain ⟨i2, _, h2 | h2⟩ := hx2 <;>
      subst h1 <;> simp at h2 <;> exact hne h2.1

private lemma words_card {d t r : Nat} :
    (Finset.univ.filter (fun F : Fin (2 ^ d) → Finset (Fin t) => ∀ z, (F z).card = r + 1)).card =
      (t.choose (r + 1)) ^ (2 ^ d) := by
  classical
  let pc : Finset (Finset (Fin t)) := Finset.powersetCard (r + 1) (Finset.univ : Finset (Fin t))
  have heq : Finset.univ.filter (fun F : Fin (2 ^ d) → Finset (Fin t) => ∀ z, (F z).card = r + 1) =
      Fintype.piFinset (fun _ : Fin (2 ^ d) => pc) := by
    ext F
    simp [pc, Fintype.mem_piFinset, mem_powersetCard]
  rw [heq, Fintype.card_piFinset]
  simp only [pc, card_powersetCard, card_univ, Fintype.card_fin, prod_const]

private lemma prime_represents {d t r : Nat}
    (X : Finset (Fin (2 ^ d) × (Fin t × Bool))) :
    (∃ z : Fin (2 ^ d), (missing X z).card ≤ r) ↔
      ∀ C ∈ (Finset.univ.filter (fun F : Fin (2 ^ d) → Finset (Fin t) =>
        ∀ z, (F z).card = r + 1)).image mkClause, (C ∩ X).Nonempty := by
  classical
  constructor
  · rintro ⟨z, hz⟩ C hC
    obtain ⟨F, hF, rfl⟩ := mem_image.mp hC
    have hFc : (F z).card = r + 1 := (mem_filter.mp hF).2 z
    have hnot : ¬ F z ⊆ missing X z := by
      intro hsub
      have hle := card_le_card hsub
      omega
    obtain ⟨i, hiF, hiM⟩ := not_subset.mp hnot
    simp only [missing, mem_filter, mem_univ, true_and, not_and, not_not] at hiM
    by_cases hf : (z, i, false) ∈ X
    · exact ⟨(z, i, false), mem_inter.mpr ⟨by simp [mkClause, hiF], hf⟩⟩
    · exact ⟨(z, i, true), mem_inter.mpr ⟨by simp [mkClause, hiF], hiM hf⟩⟩
  · intro hall
    by_contra hno
    push Not at hno
    have hex : ∀ z : Fin (2 ^ d), ∃ s ⊆ missing X z, s.card = r + 1 :=
      fun z => exists_subset_card_eq (by have := hno z; omega)
    choose F hFsub hFcard using hex
    have hFmem : F ∈ Finset.univ.filter (fun G : Fin (2 ^ d) → Finset (Fin t) =>
        ∀ z, (G z).card = r + 1) := by
      simp [hFcard]
    obtain ⟨⟨z, i, b⟩, hv⟩ := hall (mkClause F) (mem_image_of_mem mkClause hFmem)
    rw [mem_inter] at hv
    have hiF : i ∈ F z := (mem_filter.mp hv.1).2
    have hiM := (mem_filter.mp (hFsub z hiF)).2
    cases b
    · exact hiM.1 hv.2
    · exact hiM.2 hv.2

private lemma prime_subset {d t r : Nat}
    (H : Finset (Finset (Fin (2 ^ d) × (Fin t × Bool))))
    (hH : ∀ X, (∃ z : Fin (2 ^ d), (missing X z).card ≤ r) ↔
      ∀ C ∈ H, (C ∩ X).Nonempty) :
    (Finset.univ.filter (fun F : Fin (2 ^ d) → Finset (Fin t) =>
      ∀ z, (F z).card = r + 1)).image mkClause ⊆ H := by
  classical
  intro C hC
  obtain ⟨F, hF, rfl⟩ := mem_image.mp hC
  have hFc : ∀ z, (F z).card = r + 1 := (mem_filter.mp hF).2
  let X : Finset (Fin (2 ^ d) × (Fin t × Bool)) := Finset.univ \ mkClause F
  have hnok : ¬ ∃ z : Fin (2 ^ d), (missing X z).card ≤ r := by
    rintro ⟨z, hz⟩
    have hsub : F z ⊆ missing X z := by
      intro i hi
      simp [missing, X, mkClause, hi]
    have hle := card_le_card hsub
    have := hFc z
    omega
  have hnotall : ¬ ∀ D ∈ H, (D ∩ X).Nonempty := fun h => hnok ((hH X).mpr h)
  push Not at hnotall
  obtain ⟨D, hDH, hDX⟩ := hnotall
  have hDsub : D ⊆ mkClause F := by
    intro v hvD
    by_contra hvC
    have hvX : v ∈ X := mem_sdiff.mpr ⟨mem_univ v, hvC⟩
    have hne : v ∈ D ∩ X := mem_inter.mpr ⟨hvD, hvX⟩
    rw [hDX] at hne
    exact notMem_empty v hne
  have hCsub : mkClause F ⊆ D := by
    intro v hvC
    by_contra hvD
    let X' := insert v X
    have hDX' : D ∩ X' = ∅ := by
      ext u
      simp only [X', mem_inter, mem_insert, notMem_empty, iff_false, not_and]
      rintro huD (rfl | huX)
      · exact hvD huD
      · have hne : u ∈ D ∩ X := mem_inter.mpr ⟨huD, huX⟩
        rw [hDX] at hne
        exact notMem_empty u hne
    have hnok' : ¬ ∃ z : Fin (2 ^ d), (missing X' z).card ≤ r := by
      intro hok'
      obtain ⟨w, hw⟩ := (hH X').mp hok' D hDH
      rw [hDX'] at hw
      exact notMem_empty w hw
    apply hnok'
    refine ⟨v.1, ?_⟩
    have hsub : missing X' v.1 ⊆ (F v.1).erase v.2.1 := by
      intro i hi
      simp only [missing, X', X, mem_filter, mem_univ, true_and, mem_insert, mem_sdiff,
        not_or, not_not] at hi
      rw [mem_erase]
      constructor
      · intro heq
        rcases v with ⟨vz, vi, vb⟩
        dsimp only at heq hi
        subst heq
        cases vb
        · exact hi.1.1 rfl
        · exact hi.2.1 rfl
      · exact (mem_filter.mp hi.1.2).2
    have hvi : v.2.1 ∈ F v.1 := (mem_filter.mp hvC).2
    have hcard := card_le_card hsub
    rw [card_erase_of_mem hvi, hFc v.1] at hcard
    omega
  have heq : D = mkClause F := Subset.antisymm hDsub hCsub
  rwa [← heq]

private def primeSet (d t r : Nat) : Finset (Finset (Fin (2 ^ d) × (Fin t × Bool))) :=
  (Finset.univ.filter (fun F : Fin (2 ^ d) → Finset (Fin t) => ∀ z, (F z).card = r + 1)).image
    mkClause

private def interSet {d t : Nat} (C X : Finset (Fin (2 ^ d) × (Fin t × Bool))) :
    Finset (Fin (2 ^ d) × (Fin t × Bool)) :=
  C ∩ X

private lemma primeSet_card (d t r : Nat) :
    (primeSet d t r).card = (t.choose (r + 1)) ^ (2 ^ d) := by
  unfold primeSet
  rw [card_image_of_injective _ mkClause_inj]
  exact words_card

private lemma primeSet_elem_card (d t r : Nat) :
    ∀ C ∈ primeSet d t r, C.card = 2 * (r + 1) * 2 ^ d := by
  intro C hC
  obtain ⟨F, hF, rfl⟩ := mem_image.mp hC
  exact mkClause_card (mem_filter.mp hF).2

end Comb

section Graph

private lemma sum_two_pow_lt (d : Nat) (f : Fin d → Bool) :
    (∑ k : Fin d, if f k then 2 ^ k.val else 0) < 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun k => f k.castSucc)
    have h2 : (if f (Fin.last d) then 2 ^ d else 0) ≤ 2 ^ d := by split_ifs <;> omega
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    simp only [Fin.val_castSucc, Fin.val_last]
    omega

private lemma testBit_sum_two_pow (d : Nat) (f : Fin d → Bool) (j : Fin d) :
    (∑ k : Fin d, if f k then 2 ^ k.val else 0).testBit j.val = f j := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    let S := ∑ k : Fin d, if f k.castSucc then 2 ^ k.val else 0
    have hS : S < 2 ^ d := sum_two_pow_lt d (fun k => f k.castSucc)
    change (S + if f (Fin.last d) then 2 ^ d else 0).testBit j.val = f j
    cases hlast : f (Fin.last d)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      by_cases hj : j.val < d
      · have := ih (fun k => f k.castSucc) ⟨j.val, hj⟩
        simpa [S, Fin.castSucc] using this
      · have hjeq : j = Fin.last d := Fin.ext (by have := j.isLt; simp [Fin.val_last]; omega)
        subst hjeq
        rw [hlast]
        exact Nat.testBit_lt_two_pow hS
    · simp only [↓reduceIte]
      have hor : S + 2 ^ d = S ||| 2 ^ d := by
        rw [Nat.add_comm, ← Nat.mul_one (2 ^ d), Nat.two_pow_add_eq_or_of_lt hS]
        simp [Nat.or_comm]
      rw [hor, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases hj : j.val < d
      · have hne : d ≠ j.val := by omega
        simp only [decide_eq_false hne, Bool.or_false]
        have := ih (fun k => f k.castSucc) ⟨j.val, hj⟩
        simpa [S, Fin.castSucc] using this
      · have hjeq : j = Fin.last d := Fin.ext (by have := j.isLt; simp [Fin.val_last]; omega)
        subst hjeq
        simp [hlast]

private lemma exists_testBit_ne {d : Nat} (a b : Fin (2 ^ d)) (hne : a ≠ b) :
    ∃ k : Fin d, a.val.testBit k.val ≠ b.val.testBit k.val := by
  by_contra hall
  push Not at hall
  apply hne
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < d
  · exact hall ⟨k, hk⟩
  · have hpow : 2 ^ d ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hpow)]

private def nVert (d t : Nat) : Nat := 3 * d + 4 * (2 ^ d * t)

private lemma idx_lt {d t : Nat} (z : Fin (2 ^ d)) (i : Fin t) (off : Nat) (hoff : off < 4) :
    3 * d + 4 * (z.val * t + i.val) + off < nVert d t := by
  unfold nVert
  have h1 : z.val * t + i.val < 2 ^ d * t := by
    have hz : z.val + 1 ≤ 2 ^ d := z.isLt
    have hm : (z.val + 1) * t ≤ 2 ^ d * t := Nat.mul_le_mul_right t hz
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega
  omega

private def vU {d t : Nat} (k : Fin d) : Fin (nVert d t) :=
  ⟨k.val, by unfold nVert; omega⟩

private def vU0 {d t : Nat} (k : Fin d) : Fin (nVert d t) :=
  ⟨d + k.val, by unfold nVert; omega⟩

private def vU1 {d t : Nat} (k : Fin d) : Fin (nVert d t) :=
  ⟨2 * d + k.val, by unfold nVert; omega⟩

private def vS {d t : Nat} (z : Fin (2 ^ d)) (i : Fin t) : Fin (nVert d t) :=
  ⟨3 * d + 4 * (z.val * t + i.val), idx_lt z i 0 (by omega)⟩

private def vT {d t : Nat} (z : Fin (2 ^ d)) (i : Fin t) : Fin (nVert d t) :=
  ⟨3 * d + 4 * (z.val * t + i.val) + 1, idx_lt z i 1 (by omega)⟩

private def vX {d t : Nat} (z : Fin (2 ^ d)) (i : Fin t) : Fin (nVert d t) :=
  ⟨3 * d + 4 * (z.val * t + i.val) + 2, idx_lt z i 2 (by omega)⟩

private def vY {d t : Nat} (z : Fin (2 ^ d)) (i : Fin t) : Fin (nVert d t) :=
  ⟨3 * d + 4 * (z.val * t + i.val) + 3, idx_lt z i 3 (by omega)⟩

private def Wbig (d t : Nat) : Nat := 2 ^ d * t + 1

private def wt (d t : Nat) (v : Fin (nVert d t)) : Nat :=
  if v.val < d then 2 * Wbig d t else if v.val < 3 * d then Wbig d t else 1

private lemma wt_of_lt {d t : Nat} (v : Fin (nVert d t)) (h : v.val < d) :
    wt d t v = 2 * Wbig d t := by
  unfold wt; simp [h]

private lemma wt_of_mid {d t : Nat} (v : Fin (nVert d t)) (h1 : ¬ v.val < d) (h2 : v.val < 3 * d) :
    wt d t v = Wbig d t := by
  unfold wt; simp [h1, h2]

private lemma wt_of_ge {d t : Nat} (v : Fin (nVert d t)) (h1 : ¬ v.val < d) (h2 : ¬ v.val < 3 * d) :
    wt d t v = 1 := by
  unfold wt; simp [h1, h2]

private lemma blk_idx_inj {d t : Nat} {z1 z2 : Fin (2 ^ d)} {i1 i2 : Fin t}
    (h : z1.val * t + i1.val = z2.val * t + i2.val) : z1 = z2 ∧ i1 = i2 := by
  have hi1 := i1.isLt
  have hi2 := i2.isLt
  have hz : z1.val = z2.val := by nlinarith
  have hi : i1.val = i2.val := by nlinarith
  exact ⟨Fin.ext hz, Fin.ext hi⟩

private def Dset (d t : Nat) : Finset (Fin (nVert d t)) :=
  Finset.univ.filter (fun v : Fin (nVert d t) => v.val < d)

private def Sset (d t : Nat) : Finset (Fin (nVert d t)) :=
  Finset.univ.filter (fun v : Fin (nVert d t) =>
    (d ≤ v.val ∧ v.val < 2 * d) ∨ (3 * d ≤ v.val ∧ 2 ≤ (v.val - 3 * d) % 4))

private def pinMap (d t : Nat) (v : Fin (2 ^ d) × (Fin t × Bool)) : Fin (nVert d t) × Bool :=
  match v.2.2 with
  | false => (vS v.1 v.2.1, true)
  | true => (vT v.1 v.2.1, false)

private def selEdges (d t : Nat) : Finset (Fin (nVert d t) × Fin (nVert d t)) :=
  (Finset.univ : Finset (Fin d)).biUnion (fun k => {(vU k, vU0 k), (vU k, vU1 k)})

private def blkEdges (d t : Nat) : Finset (Fin (nVert d t) × Fin (nVert d t)) :=
  ((Finset.univ : Finset (Fin (2 ^ d))) ×ˢ (Finset.univ : Finset (Fin t))).biUnion
    (fun p => {(vT p.1 p.2, vX p.1 p.2), (vS p.1 p.2, vY p.1 p.2), (vT p.1 p.2, vY p.1 p.2)})

private def crossEdges (d t : Nat) : Finset (Fin (nVert d t) × Fin (nVert d t)) :=
  ((Finset.univ : Finset (Fin d)) ×ˢ
    ((Finset.univ : Finset (Fin (2 ^ d))) ×ˢ (Finset.univ : Finset (Fin t)))).biUnion
    (fun q =>
      if q.2.1.val.testBit q.1.val then
        {(vU q.1, vS q.2.1 q.2.2), (vU q.1, vX q.2.1 q.2.2), (vU q.1, vY q.2.1 q.2.2)}
      else
        {(vU0 q.1, vS q.2.1 q.2.2), (vU1 q.1, vX q.2.1 q.2.2), (vU1 q.1, vY q.2.1 q.2.2)})

private def Ggraph (d t : Nat) : Finset (Fin (nVert d t) × Fin (nVert d t)) :=
  selEdges d t ∪ blkEdges d t ∪ crossEdges d t

private lemma pinMap_inj (d t : Nat) :
    Function.Injective (fun v : Fin (2 ^ d) × (Fin t × Bool) => (pinMap d t v).1) := by
  rintro ⟨z1, i1, b1⟩ ⟨z2, i2, b2⟩ h
  have hval : (pinMap d t (z1, i1, b1)).1.val = (pinMap d t (z2, i2, b2)).1.val :=
    congrArg Fin.val h
  cases b1 <;> cases b2 <;> simp only [pinMap, vS, vT] at hval
  · have hlin : z1.val * t + i1.val = z2.val * t + i2.val := by omega
    have hi1 := i1.isLt
    have hi2 := i2.isLt
    have hz : z1.val = z2.val := by nlinarith
    have hi : i1.val = i2.val := by nlinarith
    exact Prod.ext (Fin.ext hz) (Prod.ext (Fin.ext hi) rfl)
  · omega
  · omega
  · have hlin : z1.val * t + i1.val = z2.val * t + i2.val := by omega
    have hi1 := i1.isLt
    have hi2 := i2.isLt
    have hz : z1.val = z2.val := by nlinarith
    have hi : i1.val = i2.val := by nlinarith
    exact Prod.ext (Fin.ext hz) (Prod.ext (Fin.ext hi) rfl)

private lemma Ggraph_lt (d t : Nat) :
    ∀ e ∈ Ggraph d t, e.1 < e.2 := by
  intro e he
  simp only [Ggraph, mem_union, selEdges, blkEdges, crossEdges, mem_biUnion, mem_univ,
    mem_product, true_and] at he
  rcases he with (⟨k, hk⟩ | ⟨⟨z, i⟩, hzi⟩) | ⟨⟨k, z, i⟩, hkzi⟩
  · simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact Fin.mk_lt_mk.mpr (by omega)
  · simp only [mem_insert, mem_singleton] at hzi
    rcases hzi with rfl | rfl | rfl <;> exact Fin.mk_lt_mk.mpr (by omega)
  · split_ifs at hkzi
    · simp only [mem_insert, mem_singleton] at hkzi
      rcases hkzi with rfl | rfl | rfl <;> exact Fin.mk_lt_mk.mpr (by omega)
    · simp only [mem_insert, mem_singleton] at hkzi
      rcases hkzi with rfl | rfl | rfl <;> exact Fin.mk_lt_mk.mpr (by omega)

private lemma wt_pos (d t : Nat) : ∀ v : Fin (nVert d t), 0 < wt d t v := by
  intro v
  unfold wt Wbig
  split_ifs <;> omega

private lemma Dset_card (d t : Nat) : (Dset d t).card = d := by
  have heq : Dset d t = (Finset.univ : Finset (Fin d)).image (fun k => vU (t := t) k) := by
    ext v
    simp only [Dset, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hv
      exact ⟨⟨v.val, hv⟩, Fin.ext rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.isLt
  rw [heq, card_image_of_injective]
  · simp
  · intro a b h
    exact Fin.ext (congrArg (Fin.val : Fin (nVert d t) → Nat) h)

private lemma Ggraph_bip (d t : Nat) :
    ∀ e ∈ Ggraph d t, e.1 ∉ Dset d t → e.2 ∉ Dset d t →
      (e.1 ∈ Sset d t ↔ e.2 ∉ Sset d t) := by
  intro e he h1 h2
  simp only [Dset, mem_filter, mem_univ, true_and, not_lt] at h1 h2
  simp only [Ggraph, mem_union, selEdges, blkEdges, crossEdges, mem_biUnion, mem_univ,
    mem_product, true_and] at he
  rcases he with (⟨k, hk⟩ | ⟨⟨z, i⟩, hzi⟩) | ⟨⟨k, z, i⟩, hkzi⟩
  · simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl <;> (dsimp [vU] at h1; omega)
  · simp only [mem_insert, mem_singleton] at hzi
    rcases hzi with rfl | rfl | rfl <;>
      (simp only [Sset, mem_filter, mem_univ, true_and, vS, vT, vX, vY]; omega)
  · split_ifs at hkzi
    · simp only [mem_insert, mem_singleton] at hkzi
      rcases hkzi with rfl | rfl | rfl <;> (dsimp [vU] at h1; omega)
    · simp only [mem_insert, mem_singleton] at hkzi
      rcases hkzi with rfl | rfl | rfl <;>
        (simp only [Sset, mem_filter, mem_univ, true_and, vU0, vU1, vS, vX, vY]; omega)

private def selCost {d t : Nat} (C : Finset (Fin (nVert d t))) (k : Fin d) : Nat :=
  (if vU k ∈ C then 2 * Wbig d t else 0) +
  (if vU0 k ∈ C then Wbig d t else 0) +
  (if vU1 k ∈ C then Wbig d t else 0)

private def blkCost {d t : Nat} (C : Finset (Fin (nVert d t))) (z : Fin (2 ^ d)) (i : Fin t) :
    Nat :=
  (if vS z i ∈ C then 1 else 0) +
  (if vT z i ∈ C then 1 else 0) +
  (if vX z i ∈ C then 1 else 0) +
  (if vY z i ∈ C then 1 else 0)

private lemma sum_wt_decomp {d t : Nat} (C : Finset (Fin (nVert d t))) :
    C.sum (wt d t) =
      (∑ k : Fin d, selCost C k) +
      ∑ z : Fin (2 ^ d), ∑ i : Fin t, blkCost C z i := by
  classical
  have h1 : C.sum (wt d t) = ∑ v : Fin (nVert d t), if v ∈ C then wt d t v else 0 := by
    rw [sum_ite_mem, univ_inter]
  rw [h1]
  let f : Fin (nVert d t) → Nat := fun v => if v ∈ C then wt d t v else 0
  let sSel : Fin d → Finset (Fin (nVert d t)) := fun k => {vU k, vU0 k, vU1 k}
  let sBlk : Fin (2 ^ d) × Fin t → Finset (Fin (nVert d t)) :=
    fun p => {vS p.1 p.2, vT p.1 p.2, vX p.1 p.2, vY p.1 p.2}
  let A : Finset (Fin (nVert d t)) := Finset.univ.biUnion sSel
  let B : Finset (Fin (nVert d t)) := (Finset.univ ×ˢ Finset.univ).biUnion sBlk
  have hAB : Disjoint A B := by
    rw [disjoint_left]
    intro v hvA hvB
    simp only [A, B, sSel, sBlk, mem_biUnion, mem_univ, mem_product, true_and, mem_insert,
      mem_singleton] at hvA hvB
    obtain ⟨k, rfl | rfl | rfl⟩ := hvA <;> obtain ⟨⟨z, i⟩, h | h | h | h⟩ := hvB <;>
      have hv := congrArg Fin.val h <;> dsimp [vU, vU0, vU1, vS, vT, vX, vY] at hv <;> omega
  have huniv : (Finset.univ : Finset (Fin (nVert d t))) = A ∪ B := by
    ext v
    simp only [mem_univ, mem_union, true_iff]
    by_cases hlt : v.val < 3 * d
    · left
      simp only [A, sSel, mem_biUnion, mem_univ, true_and, mem_insert, mem_singleton]
      by_cases h0 : v.val < d
      · exact ⟨⟨v.val, h0⟩, Or.inl (Fin.ext rfl)⟩
      · by_cases h2 : v.val < 2 * d
        · exact ⟨⟨v.val - d, by omega⟩, Or.inr (Or.inl (Fin.ext (by dsimp [vU0]; omega)))⟩
        · exact ⟨⟨v.val - 2 * d, by omega⟩, Or.inr (Or.inr (Fin.ext (by dsimp [vU1]; omega)))⟩
    · right
      simp only [B, sBlk, mem_biUnion, mem_product, mem_univ, true_and, mem_insert, mem_singleton]
      have htpos : 0 < t := by
        by_contra ht0
        have ht0' : t = 0 := by omega
        have hvlt := v.isLt
        unfold nVert at hvlt
        have hmul : 2 ^ d * t = 0 := by rw [ht0', Nat.mul_zero]
        omega
      let q := (v.val - 3 * d) / 4
      let rem := (v.val - 3 * d) % 4
      have hq : q < 2 ^ d * t := by
        have hvlt := v.isLt
        unfold nVert at hvlt
        omega
      have hz : q / t < 2 ^ d := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hq)
      have hi : q % t < t := Nat.mod_lt q htpos
      have hdiv : (q / t) * t + q % t = q := by rw [Nat.mul_comm]; exact Nat.div_add_mod q t
      refine ⟨(⟨q / t, hz⟩, ⟨q % t, hi⟩), ?_⟩
      have hrem : rem = 0 ∨ rem = 1 ∨ rem = 2 ∨ rem = 3 := by omega
      rcases hrem with hr | hr | hr | hr
      · left; exact Fin.ext (by dsimp [vS]; omega)
      · right; left; exact Fin.ext (by dsimp [vT]; omega)
      · right; right; left; exact Fin.ext (by dsimp [vX]; omega)
      · right; right; right; exact Fin.ext (by dsimp [vY]; omega)
  rw [huniv, sum_union hAB]
  congr 1
  · rw [sum_biUnion]
    · apply sum_congr rfl
      intro k _
      have hne01 : vU (t := t) k ≠ vU0 k := fun h => by
        have := congrArg Fin.val h; dsimp [vU, vU0] at this; omega
      have hne02 : vU (t := t) k ≠ vU1 k := fun h => by
        have := congrArg Fin.val h; dsimp [vU, vU1] at this; omega
      have hne12 : vU0 (t := t) k ≠ vU1 k := fun h => by
        have := congrArg Fin.val h; dsimp [vU0, vU1] at this; omega
      simp only [sSel, sum_insert, mem_insert, mem_singleton, hne01, hne02, hne12, or_self,
        not_false_eq_true, sum_singleton]
      have hw0 : wt d t (vU k) = 2 * Wbig d t := wt_of_lt (vU k) k.isLt
      have hw1 : wt d t (vU0 k) = Wbig d t :=
        wt_of_mid (vU0 k) (by dsimp [vU0]; omega) (by dsimp [vU0]; have := k.isLt; omega)
      have hw2 : wt d t (vU1 k) = Wbig d t :=
        wt_of_mid (vU1 k) (by dsimp [vU1]; omega) (by dsimp [vU1]; have := k.isLt; omega)
      simp only [hw0, hw1, hw2, selCost]
      omega
    · intro k1 _ k2 _ hne
      dsimp only [Function.onFun]
      rw [disjoint_left]
      intro v hv1 hv2
      simp only [sSel, mem_insert, mem_singleton] at hv1 hv2
      rcases hv1 with rfl | rfl | rfl <;> rcases hv2 with h | h | h <;>
        have hv := congrArg Fin.val h <;> dsimp [vU, vU0, vU1] at hv <;>
        exact hne (Fin.ext (by omega))
  · rw [sum_biUnion, sum_product]
    · apply sum_congr rfl
      intro z _
      apply sum_congr rfl
      intro i _
      have hst : vS z i ≠ vT z i := fun h => by
        have := congrArg Fin.val h; dsimp [vS, vT] at this; omega
      have hsx : vS z i ≠ vX z i := fun h => by
        have := congrArg Fin.val h; dsimp [vS, vX] at this; omega
      have hsy : vS z i ≠ vY z i := fun h => by
        have := congrArg Fin.val h; dsimp [vS, vY] at this; omega
      have htx : vT z i ≠ vX z i := fun h => by
        have := congrArg Fin.val h; dsimp [vT, vX] at this; omega
      have hty : vT z i ≠ vY z i := fun h => by
        have := congrArg Fin.val h; dsimp [vT, vY] at this; omega
      have hxy : vX z i ≠ vY z i := fun h => by
        have := congrArg Fin.val h; dsimp [vX, vY] at this; omega
      simp only [sBlk, sum_insert, mem_insert, mem_singleton, hst, hsx, hsy, htx, hty, hxy,
        or_self, not_false_eq_true, sum_singleton]
      have hws : wt d t (vS z i) = 1 :=
        wt_of_ge (vS z i) (by dsimp [vS]; omega) (by dsimp [vS]; omega)
      have hwt : wt d t (vT z i) = 1 :=
        wt_of_ge (vT z i) (by dsimp [vT]; omega) (by dsimp [vT]; omega)
      have hwx : wt d t (vX z i) = 1 :=
        wt_of_ge (vX z i) (by dsimp [vX]; omega) (by dsimp [vX]; omega)
      have hwy : wt d t (vY z i) = 1 :=
        wt_of_ge (vY z i) (by dsimp [vY]; omega) (by dsimp [vY]; omega)
      simp only [hws, hwt, hwx, hwy, blkCost]
      omega
    · intro p1 _ p2 _ hne
      dsimp only [Function.onFun]
      rw [disjoint_left]
      intro v hv1 hv2
      simp only [sBlk, mem_insert, mem_singleton] at hv1 hv2
      rcases hv1 with rfl | rfl | rfl | rfl <;> rcases hv2 with h | h | h | h <;>
        have hv := congrArg Fin.val h <;> dsimp [vS, vT, vX, vY] at hv <;>
        (obtain ⟨hz, hi⟩ := @blk_idx_inj d t p1.1 p2.1 p1.2 p2.2 (by omega)
         exact hne (Prod.ext hz hi))

private def baseCover (d t : Nat) (z0 : Fin (2 ^ d))
    (X : Finset (Fin (2 ^ d) × (Fin t × Bool))) : Finset (Fin (nVert d t)) :=
  let sel : Finset (Fin (nVert d t)) :=
    (Finset.univ : Finset (Fin d)).biUnion (fun k =>
      if z0.val.testBit k.val then {vU k} else {vU0 k, vU1 k})
  let blks : Finset (Fin (nVert d t)) :=
    ((Finset.univ : Finset (Fin (2 ^ d))) ×ˢ (Finset.univ : Finset (Fin t))).biUnion (fun p =>
      if p.1 = z0 then
        if (z0, p.2, false) ∈ X then {vX p.1 p.2, vY p.1 p.2}
        else if (z0, p.2, true) ∈ X then {vS p.1 p.2, vT p.1 p.2}
        else {vS p.1 p.2, vX p.1 p.2, vY p.1 p.2}
      else {vS p.1 p.2, vX p.1 p.2, vY p.1 p.2})
  sel ∪ blks

private lemma mem_baseCover_sel {d t : Nat} (z0 : Fin (2 ^ d))
    (X : Finset (Fin (2 ^ d) × (Fin t × Bool))) (k : Fin d) :
    (vU k ∈ baseCover d t z0 X ↔ z0.val.testBit k.val = true) ∧
    (vU0 k ∈ baseCover d t z0 X ↔ z0.val.testBit k.val = false) ∧
    (vU1 k ∈ baseCover d t z0 X ↔ z0.val.testBit k.val = false) := by
  have hnotB : ∀ w : Fin (nVert d t), w.val < 3 * d →
      w ∉ ((Finset.univ : Finset (Fin (2 ^ d))) ×ˢ (Finset.univ : Finset (Fin t))).biUnion
        (fun p => if p.1 = z0 then
            if (z0, p.2, false) ∈ X then {vX p.1 p.2, vY p.1 p.2}
            else if (z0, p.2, true) ∈ X then {vS p.1 p.2, vT p.1 p.2}
            else {vS p.1 p.2, vX p.1 p.2, vY p.1 p.2}
          else {vS p.1 p.2, vX p.1 p.2, vY p.1 p.2}) := by
    intro w hw hmem
    simp only [mem_biUnion, mem_product, mem_univ, true_and] at hmem
    obtain ⟨⟨z, i⟩, hzi⟩ := hmem
    split_ifs at hzi <;> simp only [mem_insert, mem_singleton] at hzi <;>
      rcases hzi with rfl | rfl | rfl <;> dsimp [vS, vT, vX, vY] at hw <;> omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [baseCover, mem_union, hnotB (vU k) (by dsimp [vU]; omega), or_false,
      mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      split_ifs at hj with hb
      · rw [mem_singleton] at hj
        have hjk : j = k := Fin.ext (by have := congrArg Fin.val hj; dsimp [vU] at this; omega)
        subst hjk; exact hb
      · simp only [mem_insert, mem_singleton] at hj
        rcases hj with h | h <;> have := congrArg Fin.val h <;>
          dsimp [vU, vU0, vU1] at this <;> omega
    · intro hb
      exact ⟨k, by simp [hb]⟩
  · simp only [baseCover, mem_union, hnotB (vU0 k) (by dsimp [vU0]; omega), or_false,
      mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      split_ifs at hj with hb
      · rw [mem_singleton] at hj
        have := congrArg Fin.val hj; dsimp [vU, vU0] at this; omega
      · simp only [mem_insert, mem_singleton] at hj
        rcases hj with h | h
        · have hjk : j = k := Fin.ext (by have := congrArg Fin.val h; dsimp [vU0] at this; omega)
          subst hjk; exact Bool.eq_false_iff.mpr hb
        · have := congrArg Fin.val h; dsimp [vU0, vU1] at this; omega
    · intro hb
      exact ⟨k, by simp [hb]⟩
  · simp only [baseCover, mem_union, hnotB (vU1 k) (by dsimp [vU1]; omega), or_false,
      mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      split_ifs at hj with hb
      · rw [mem_singleton] at hj
        have := congrArg Fin.val hj; dsimp [vU, vU1] at this; omega
      · simp only [mem_insert, mem_singleton] at hj
        rcases hj with h | h
        · have := congrArg Fin.val h; dsimp [vU0, vU1] at this; omega
        · have hjk : j = k := Fin.ext (by have := congrArg Fin.val h; dsimp [vU1] at this; omega)
          subst hjk; exact Bool.eq_false_iff.mpr hb
    · intro hb
      exact ⟨k, by simp [hb]⟩

private lemma mem_baseCover_blk {d t : Nat} (z0 : Fin (2 ^ d))
    (X : Finset (Fin (2 ^ d) × (Fin t × Bool))) (z : Fin (2 ^ d)) (i : Fin t) :
    (vS z i ∈ baseCover d t z0 X ↔ ¬ (z = z0 ∧ (z0, i, false) ∈ X)) ∧
    (vT z i ∈ baseCover d t z0 X ↔ z = z0 ∧ (z0, i, false) ∉ X ∧ (z0, i, true) ∈ X) ∧
    (vX z i ∈ baseCover d t z0 X ↔ ¬ (z = z0 ∧ (z0, i, false) ∉ X ∧ (z0, i, true) ∈ X)) ∧
    (vY z i ∈ baseCover d t z0 X ↔ ¬ (z = z0 ∧ (z0, i, false) ∉ X ∧ (z0, i, true) ∈ X)) := by
  have hnotS : ∀ w : Fin (nVert d t), 3 * d ≤ w.val →
      w ∉ (Finset.univ : Finset (Fin d)).biUnion (fun k =>
        if z0.val.testBit k.val then {vU k} else {vU0 k, vU1 k}) := by
    intro w hw hmem
    simp only [mem_biUnion, mem_univ, true_and] at hmem
    obtain ⟨k, hk⟩ := hmem
    split_ifs at hk <;> simp only [mem_insert, mem_singleton] at hk <;>
      rcases hk with rfl | rfl <;> dsimp [vU, vU0, vU1] at hw <;> omega
  have huniq : ∀ (w : Fin (nVert d t)) (z' : Fin (2 ^ d)) (i' : Fin t),
      (w = vS z' i' ∨ w = vT z' i' ∨ w = vX z' i' ∨ w = vY z' i') →
      (w = vS z i ∨ w = vT z i ∨ w = vX z i ∨ w = vY z i) →
      z' = z ∧ i' = i := by
    intro w z' i' h1 h2
    rcases h1 with rfl | rfl | rfl | rfl <;> rcases h2 with h | h | h | h <;>
      have hv := congrArg Fin.val h <;> dsimp [vS, vT, vX, vY] at hv <;>
      exact blk_idx_inj (by omega)
  have hblk_iff : ∀ w : Fin (nVert d t), 3 * d ≤ w.val →
      (w = vS z i ∨ w = vT z i ∨ w = vX z i ∨ w = vY z i) →
      (w ∈ baseCover d t z0 X ↔
        w ∈ (if z = z0 then
          if (z0, i, false) ∈ X then {vX z i, vY z i}
          else if (z0, i, true) ∈ X then {vS z i, vT z i}
          else {vS z i, vX z i, vY z i}
        else {vS z i, vX z i, vY z i} : Finset (Fin (nVert d t)))) := by
    intro w hw hpos
    simp only [baseCover, mem_union, hnotS w hw, false_or, mem_biUnion, mem_product, mem_univ,
      true_and]
    constructor
    · rintro ⟨⟨z', i'⟩, hzi'⟩
      have hpos' : w = vS z' i' ∨ w = vT z' i' ∨ w = vX z' i' ∨ w = vY z' i' := by
        split_ifs at hzi' <;> simp only [mem_insert, mem_singleton] at hzi' <;> tauto
      obtain ⟨rfl, rfl⟩ := huniq w z' i' hpos' hpos
      exact hzi'
    · intro hw'
      exact ⟨(z, i), hw'⟩
  have hst : vS z i ≠ vT z i := fun h => by
    have := congrArg Fin.val h; dsimp [vS, vT] at this; omega
  have hsx : vS z i ≠ vX z i := fun h => by
    have := congrArg Fin.val h; dsimp [vS, vX] at this; omega
  have hsy : vS z i ≠ vY z i := fun h => by
    have := congrArg Fin.val h; dsimp [vS, vY] at this; omega
  have htx : vT z i ≠ vX z i := fun h => by
    have := congrArg Fin.val h; dsimp [vT, vX] at this; omega
  have hty : vT z i ≠ vY z i := fun h => by
    have := congrArg Fin.val h; dsimp [vT, vY] at this; omega
  have hxy : vX z i ≠ vY z i := fun h => by
    have := congrArg Fin.val h; dsimp [vX, vY] at this; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hblk_iff (vS z i) (by dsimp [vS]; omega) (Or.inl rfl)]
    split_ifs with h1 <;> (try subst h1) <;> simp [hsx, hsy, *]
  · rw [hblk_iff (vT z i) (by dsimp [vT]; omega) (Or.inr (Or.inl rfl))]
    split_ifs with h1 <;> (try subst h1) <;> simp [hst.symm, htx, hty, *]
  · rw [hblk_iff (vX z i) (by dsimp [vX]; omega) (Or.inr (Or.inr (Or.inl rfl)))]
    split_ifs with h1 <;> (try subst h1) <;> simp [hsx.symm, htx.symm, *]
  · rw [hblk_iff (vY z i) (by dsimp [vY]; omega) (Or.inr (Or.inr (Or.inr rfl)))]
    split_ifs with h1 <;> (try subst h1) <;> simp [hsy.symm, hty.symm, *]

private lemma baseCover_covers {d t : Nat} (z0 : Fin (2 ^ d))
    (X : Finset (Fin (2 ^ d) × (Fin t × Bool))) :
    ∀ e ∈ Ggraph d t, e.1 ∈ baseCover d t z0 X ∨ e.2 ∈ baseCover d t z0 X := by
  intro e he
  simp only [Ggraph, mem_union, selEdges, blkEdges, crossEdges, mem_biUnion, mem_univ,
    mem_product, true_and] at he
  rcases he with (⟨k, hk⟩ | ⟨⟨z, i⟩, hzi⟩) | ⟨⟨k, z, i⟩, hkzi⟩
  · have hs := mem_baseCover_sel z0 X k
    simp only [mem_insert, mem_singleton] at hk
    rcases hk with rfl | rfl
    · cases hb : z0.val.testBit k.val
      · right; exact hs.2.1.mpr hb
      · left; exact hs.1.mpr hb
    · cases hb : z0.val.testBit k.val
      · right; exact hs.2.2.mpr hb
      · left; exact hs.1.mpr hb
  · have hb := mem_baseCover_blk z0 X z i
    simp only [mem_insert, mem_singleton] at hzi
    rcases hzi with rfl | rfl | rfl
    · by_cases h : z = z0 ∧ (z0, i, false) ∉ X ∧ (z0, i, true) ∈ X
      · left; exact hb.2.1.mpr h
      · right; exact hb.2.2.1.mpr h
    · by_cases h : z = z0 ∧ (z0, i, false) ∉ X ∧ (z0, i, true) ∈ X
      · left; exact hb.1.mpr (by tauto)
      · right; exact hb.2.2.2.mpr h
    · by_cases h : z = z0 ∧ (z0, i, false) ∉ X ∧ (z0, i, true) ∈ X
      · left; exact hb.2.1.mpr h
      · right; exact hb.2.2.2.mpr h
  · have hs := mem_baseCover_sel z0 X k
    have hb := mem_baseCover_blk z0 X z i
    split_ifs at hkzi with hbit
    · simp only [mem_insert, mem_singleton] at hkzi
      cases h0 : z0.val.testBit k.val
      · have hne : z ≠ z0 := fun heq => by subst heq; rw [h0] at hbit; simp at hbit
        rcases hkzi with rfl | rfl | rfl
        · right; exact hb.1.mpr (by tauto)
        · right; exact hb.2.2.1.mpr (by tauto)
        · right; exact hb.2.2.2.mpr (by tauto)
      · rcases hkzi with rfl | rfl | rfl <;> left <;> exact hs.1.mpr h0
    · simp only [mem_insert, mem_singleton] at hkzi
      cases h0 : z0.val.testBit k.val
      · rcases hkzi with rfl | rfl | rfl
        · left; exact hs.2.1.mpr h0
        · left; exact hs.2.2.mpr h0
        · left; exact hs.2.2.mpr h0
      · have hne : z ≠ z0 := fun heq => by subst heq; rw [h0] at hbit; simp at hbit
        rcases hkzi with rfl | rfl | rfl
        · right; exact hb.1.mpr (by tauto)
        · right; exact hb.2.2.1.mpr (by tauto)
        · right; exact hb.2.2.2.mpr (by tauto)

private lemma baseCover_pins {d t : Nat} (z0 : Fin (2 ^ d))
    (X : Finset (Fin (2 ^ d) × (Fin t × Bool))) :
    ∀ v : Fin (2 ^ d) × (Fin t × Bool), v ∉ X →
      ((pinMap d t v).1 ∈ baseCover d t z0 X ↔ (pinMap d t v).2 = true) := by
  rintro ⟨z, i, b⟩ hnotX
  have hb := mem_baseCover_blk z0 X z i
  cases b
  · simp only [pinMap, hb.1, iff_true]
    rintro ⟨rfl, h⟩
    exact hnotX h
  · simp only [pinMap, hb.2.1, Bool.false_eq_true, iff_false]
    rintro ⟨rfl, _, h⟩
    exact hnotX h

private lemma baseCover_sum {d t : Nat} (z0 : Fin (2 ^ d))
    (X : Finset (Fin (2 ^ d) × (Fin t × Bool))) :
    (baseCover d t z0 X).sum (wt d t) =
      2 * d * Wbig d t + (3 * 2 ^ d - 1) * t + (missing X z0).card := by
  classical
  rw [sum_wt_decomp]
  have hsel : ∑ k : Fin d, selCost (baseCover d t z0 X) k = 2 * d * Wbig d t := by
    have h1 : ∀ k : Fin d, selCost (baseCover d t z0 X) k = 2 * Wbig d t := by
      intro k
      have hs := mem_baseCover_sel z0 X k
      unfold selCost
      cases hb : z0.val.testBit k.val
      · simp [hs.1, hs.2.1, hs.2.2, hb]; omega
      · simp [hs.1, hs.2.1, hs.2.2, hb]
    rw [sum_congr rfl (fun k _ => h1 k), sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have hblk_ne : ∀ z : Fin (2 ^ d), z ≠ z0 →
      ∑ i : Fin t, blkCost (baseCover d t z0 X) z i = 3 * t := by
    intro z hne
    have h1 : ∀ i : Fin t, blkCost (baseCover d t z0 X) z i = 3 := by
      intro i
      have hb := mem_baseCover_blk z0 X z i
      unfold blkCost
      simp [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hne]
    rw [sum_congr rfl (fun i _ => h1 i), sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_comm]
  have hblk_eq : ∑ i : Fin t, blkCost (baseCover d t z0 X) z0 i = 2 * t + (missing X z0).card := by
    have h1 : ∀ i : Fin t, blkCost (baseCover d t z0 X) z0 i =
        2 + if (z0, i, false) ∉ X ∧ (z0, i, true) ∉ X then 1 else 0 := by
      intro i
      have hb := mem_baseCover_blk z0 X z0 i
      unfold blkCost
      by_cases hf : (z0, i, false) ∈ X <;> by_cases ht : (z0, i, true) ∈ X <;>
        simp [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2, hf, ht]
    rw [sum_congr rfl (fun i _ => h1 i), sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul, Nat.mul_comm]
    congr 1
    rw [← card_filter]
    rfl
  rw [hsel, ← add_sum_erase _ _ (mem_univ z0), hblk_eq]
  have hrest : ∑ z ∈ Finset.univ.erase z0, ∑ i : Fin t, blkCost (baseCover d t z0 X) z i =
      (2 ^ d - 1) * (3 * t) := by
    rw [sum_congr rfl (fun z hz => hblk_ne z (mem_erase.mp hz).1), sum_const,
      card_erase_of_mem (mem_univ z0), card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hrest]
  have hpow : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have harith : (3 * 2 ^ d - 1) * t = 2 * t + (2 ^ d - 1) * (3 * t) := by
    zify [hpow, show 1 ≤ 3 * 2 ^ d by omega]
    ring
  omega

private lemma cover_lower {d t : Nat} (C : Finset (Fin (nVert d t)))
    (hcov : ∀ e ∈ Ggraph d t, e.1 ∈ C ∨ e.2 ∈ C) :
    (∀ k : Fin d, 2 * Wbig d t ≤ selCost C k) ∧
    (∀ z : Fin (2 ^ d), ∀ i : Fin t, 2 ≤ blkCost C z i) ∧
    (2 * d * Wbig d t + (3 * 2 ^ d - 1) * t ≤ C.sum (wt d t)) ∧
    ∀ (X : Finset (Fin (2 ^ d) × (Fin t × Bool))) (b : Nat),
      (∀ v : Fin (2 ^ d) × (Fin t × Bool), v ∉ X → ((pinMap d t v).1 ∈ C ↔ (pinMap d t v).2 = true)) →
      C.sum (wt d t) ≤ 2 * d * Wbig d t + (3 * 2 ^ d - 1) * t + b →
      ∃ z : Fin (2 ^ d), (missing X z).card ≤ b := by
  classical
  have hsel : ∀ k : Fin d, 2 * Wbig d t ≤ selCost C k := by
    intro k
    have he0 : (vU k, vU0 k) ∈ Ggraph d t := by
      simp only [Ggraph, mem_union, selEdges, mem_biUnion, mem_univ, true_and, mem_insert,
        mem_singleton]
      exact Or.inl (Or.inl ⟨k, Or.inl rfl⟩)
    have he1 : (vU k, vU1 k) ∈ Ggraph d t := by
      simp only [Ggraph, mem_union, selEdges, mem_biUnion, mem_univ, true_and, mem_insert,
        mem_singleton]
      exact Or.inl (Or.inl ⟨k, Or.inr rfl⟩)
    have h0 := hcov _ he0
    have h1 := hcov _ he1
    unfold selCost
    by_cases hu : vU k ∈ C
    · simp [hu]; omega
    · have h0' := h0.resolve_left hu
      have h1' := h1.resolve_left hu
      simp [hu, h0', h1']
      omega
  have hblk2 : ∀ z : Fin (2 ^ d), ∀ i : Fin t, 2 ≤ blkCost C z i := by
    intro z i
    have het : (vT z i, vX z i) ∈ Ggraph d t := by
      simp only [Ggraph, mem_union, blkEdges, mem_biUnion, mem_product, mem_univ, true_and,
        mem_insert, mem_singleton]
      exact Or.inl (Or.inr ⟨(z, i), Or.inl rfl⟩)
    have hsy : (vS z i, vY z i) ∈ Ggraph d t := by
      simp only [Ggraph, mem_union, blkEdges, mem_biUnion, mem_product, mem_univ, true_and,
        mem_insert, mem_singleton]
      exact Or.inl (Or.inr ⟨(z, i), Or.inr (Or.inl rfl)⟩)
    have hty : (vT z i, vY z i) ∈ Ggraph d t := by
      simp only [Ggraph, mem_union, blkEdges, mem_biUnion, mem_product, mem_univ, true_and,
        mem_insert, mem_singleton]
      exact Or.inl (Or.inr ⟨(z, i), Or.inr (Or.inr rfl)⟩)
    have h1 := hcov _ het
    have h2 := hcov _ hsy
    have h3 := hcov _ hty
    unfold blkCost
    by_cases hs : vS z i ∈ C
    · by_cases ht : vT z i ∈ C
      · simp [hs, ht]; omega
      · have hx := h1.resolve_left ht
        have hy := h3.resolve_left ht
        simp [hs, ht, hx, hy]
    · by_cases ht : vT z i ∈ C
      · have hy := h2.resolve_left hs
        simp [hs, ht, hy]
      · have hx := h1.resolve_left ht
        have hy := h2.resolve_left hs
        simp [hs, ht, hx, hy]
  have hblk_pin : ∀ z : Fin (2 ^ d), ∀ i : Fin t, vS z i ∈ C → vT z i ∉ C → 3 ≤ blkCost C z i := by
    intro z i hs ht
    have het : (vT z i, vX z i) ∈ Ggraph d t := by
      simp only [Ggraph, mem_union, blkEdges, mem_biUnion, mem_product, mem_univ, true_and,
        mem_insert, mem_singleton]
      exact Or.inl (Or.inr ⟨(z, i), Or.inl rfl⟩)
    have hty : (vT z i, vY z i) ∈ Ggraph d t := by
      simp only [Ggraph, mem_union, blkEdges, mem_biUnion, mem_product, mem_univ, true_and,
        mem_insert, mem_singleton]
      exact Or.inl (Or.inr ⟨(z, i), Or.inr (Or.inr rfl)⟩)
    have hx : vX z i ∈ C := (hcov _ het).resolve_left ht
    have hy : vY z i ∈ C := (hcov _ hty).resolve_left ht
    unfold blkCost
    simp [hs, ht, hx, hy]
  let zC : Fin (2 ^ d) :=
    ⟨∑ k : Fin d, if decide (vU (t := t) k ∈ C) then 2 ^ k.val else 0,
      sum_two_pow_lt d (fun k => decide (vU (t := t) k ∈ C))⟩
  have hzC_bit : ∀ k : Fin d, zC.val.testBit k.val = decide (vU (t := t) k ∈ C) :=
    fun k => testBit_sum_two_pow d (fun j => decide (vU (t := t) j ∈ C)) k
  have hcheat_bound : (∃ k : Fin d, 3 * Wbig d t ≤ selCost C k) →
      2 * d * Wbig d t + (3 * 2 ^ d - 1) * t + t + 1 ≤ C.sum (wt d t) := by
    rintro ⟨k0, hk0⟩
    rw [sum_wt_decomp]
    have hsel_sum : 2 * d * Wbig d t + Wbig d t ≤ ∑ k : Fin d, selCost C k := by
      rw [← add_sum_erase _ _ (mem_univ k0)]
      have hrest : (d - 1) * (2 * Wbig d t) ≤ ∑ k ∈ Finset.univ.erase k0, selCost C k := by
        calc (d - 1) * (2 * Wbig d t)
            = ∑ _k ∈ Finset.univ.erase k0, (2 * Wbig d t) := by
              rw [sum_const, card_erase_of_mem (mem_univ k0), card_univ, Fintype.card_fin,
                smul_eq_mul]
          _ ≤ ∑ k ∈ Finset.univ.erase k0, selCost C k := sum_le_sum (fun k _ => hsel k)
      have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 k0)
      have hm : d * (2 * Wbig d t) = 2 * Wbig d t + (d - 1) * (2 * Wbig d t) := by
        zify [hd1]; ring
      have : 2 * d * Wbig d t = d * (2 * Wbig d t) := by ring
      omega
    have hblk_sum : 2 ^ d * (2 * t) ≤ ∑ z : Fin (2 ^ d), ∑ i : Fin t, blkCost C z i := by
      calc 2 ^ d * (2 * t)
          = ∑ _z : Fin (2 ^ d), ∑ _i : Fin t, (2 : Nat) := by
            simp [sum_const, smul_eq_mul, Nat.mul_comm]
        _ ≤ ∑ z : Fin (2 ^ d), ∑ i : Fin t, blkCost C z i :=
            sum_le_sum (fun z _ => sum_le_sum (fun i _ => hblk2 z i))
    have hpow : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hW : Wbig d t = 2 ^ d * t + 1 := rfl
    have harith : (3 * 2 ^ d - 1) * t + t + 1 = Wbig d t + 2 ^ d * (2 * t) := by
      rw [hW]
      zify [show 1 ≤ 3 * 2 ^ d by omega]
      ring
    omega
  have hnocheat_ne : (∀ k : Fin d, selCost C k < 3 * Wbig d t) →
      ∀ z : Fin (2 ^ d), z ≠ zC → ∀ i : Fin t, 3 ≤ blkCost C z i := by
    intro hnc z hne i
    obtain ⟨k, hbit⟩ := exists_testBit_ne z zC hne
    rw [hzC_bit k] at hbit
    have hs : vS z i ∈ C ∧ vX z i ∈ C ∧ vY z i ∈ C := by
      cases hzb : z.val.testBit k.val
      · have hu : vU (t := t) k ∈ C := by
          rw [hzb] at hbit
          by_contra hnu
          exact hbit (by simp [hnu])
        have hlt := hnc k
        unfold selCost at hlt
        simp only [hu, ↓reduceIte] at hlt
        have hu0 : vU0 (t := t) k ∉ C := by
          intro h; simp only [h, ↓reduceIte] at hlt; omega
        have hu1 : vU1 (t := t) k ∉ C := by
          intro h; simp only [h, ↓reduceIte] at hlt; omega
        have eS : (vU0 k, vS z i) ∈ Ggraph d t := by
          simp only [Ggraph, mem_union, crossEdges, mem_biUnion, mem_product, mem_univ, true_and]
          exact Or.inr ⟨(k, z, i), by simp [hzb]⟩
        have eX : (vU1 k, vX z i) ∈ Ggraph d t := by
          simp only [Ggraph, mem_union, crossEdges, mem_biUnion, mem_product, mem_univ, true_and]
          exact Or.inr ⟨(k, z, i), by simp [hzb]⟩
        have eY : (vU1 k, vY z i) ∈ Ggraph d t := by
          simp only [Ggraph, mem_union, crossEdges, mem_biUnion, mem_product, mem_univ, true_and]
          exact Or.inr ⟨(k, z, i), by simp [hzb]⟩
        exact ⟨(hcov _ eS).resolve_left hu0, (hcov _ eX).resolve_left hu1,
          (hcov _ eY).resolve_left hu1⟩
      · have hnu : vU (t := t) k ∉ C := by
          rw [hzb] at hbit
          intro hu
          exact hbit (by simp [hu])
        have eS : (vU k, vS z i) ∈ Ggraph d t := by
          simp only [Ggraph, mem_union, crossEdges, mem_biUnion, mem_product, mem_univ, true_and]
          exact Or.inr ⟨(k, z, i), by simp [hzb]⟩
        have eX : (vU k, vX z i) ∈ Ggraph d t := by
          simp only [Ggraph, mem_union, crossEdges, mem_biUnion, mem_product, mem_univ, true_and]
          exact Or.inr ⟨(k, z, i), by simp [hzb]⟩
        have eY : (vU k, vY z i) ∈ Ggraph d t := by
          simp only [Ggraph, mem_union, crossEdges, mem_biUnion, mem_product, mem_univ, true_and]
          exact Or.inr ⟨(k, z, i), by simp [hzb]⟩
        exact ⟨(hcov _ eS).resolve_left hnu, (hcov _ eX).resolve_left hnu,
          (hcov _ eY).resolve_left hnu⟩
    unfold blkCost
    simp only [hs.1, hs.2.1, hs.2.2, ↓reduceIte]
    omega
  have hsel_all : 2 * d * Wbig d t ≤ ∑ k : Fin d, selCost C k := by
    calc 2 * d * Wbig d t
        = ∑ _k : Fin d, (2 * Wbig d t) := by
          rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; ring
      _ ≤ ∑ k : Fin d, selCost C k := sum_le_sum (fun k _ => hsel k)
  have hopt : 2 * d * Wbig d t + (3 * 2 ^ d - 1) * t ≤ C.sum (wt d t) := by
    by_cases hch : ∃ k : Fin d, 3 * Wbig d t ≤ selCost C k
    · have := hcheat_bound hch; omega
    · push Not at hch
      rw [sum_wt_decomp, ← add_sum_erase _ _ (mem_univ zC)]
      have hzC_sum : 2 * t ≤ ∑ i : Fin t, blkCost C zC i := by
        calc 2 * t = ∑ _i : Fin t, (2 : Nat) := by
              rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
          _ ≤ ∑ i : Fin t, blkCost C zC i := sum_le_sum (fun i _ => hblk2 zC i)
      have hrest : (2 ^ d - 1) * (3 * t) ≤
          ∑ z ∈ Finset.univ.erase zC, ∑ i : Fin t, blkCost C z i := by
        calc (2 ^ d - 1) * (3 * t)
            = ∑ _z ∈ Finset.univ.erase zC, ∑ _i : Fin t, (3 : Nat) := by
              simp [sum_const, card_erase_of_mem (mem_univ zC), smul_eq_mul, Nat.mul_comm]
          _ ≤ ∑ z ∈ Finset.univ.erase zC, ∑ i : Fin t, blkCost C z i :=
              sum_le_sum (fun z hz => sum_le_sum (fun i _ =>
                hnocheat_ne hch z (mem_erase.mp hz).1 i))
      have hpow : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      have harith : (3 * 2 ^ d - 1) * t = 2 * t + (2 ^ d - 1) * (3 * t) := by
        zify [hpow, show 1 ≤ 3 * 2 ^ d by omega]; ring
      omega
  refine ⟨hsel, hblk2, hopt, ?_⟩
  intro X b hpins hle
  by_cases hch : ∃ k : Fin d, 3 * Wbig d t ≤ selCost C k
  · have hbig := hcheat_bound hch
    refine ⟨zC, ?_⟩
    have hcard : (missing X zC).card ≤ t := by
      calc (missing X zC).card ≤ (Finset.univ : Finset (Fin t)).card := card_le_card (filter_subset _ _)
        _ = t := by simp
    omega
  · push Not at hch
    refine ⟨zC, ?_⟩
    rw [sum_wt_decomp, ← add_sum_erase _ _ (mem_univ zC)] at hle
    have hrest : (2 ^ d - 1) * (3 * t) ≤
        ∑ z ∈ Finset.univ.erase zC, ∑ i : Fin t, blkCost C z i := by
      calc (2 ^ d - 1) * (3 * t)
          = ∑ _z ∈ Finset.univ.erase zC, ∑ _i : Fin t, (3 : Nat) := by
            simp [sum_const, card_erase_of_mem (mem_univ zC), smul_eq_mul, Nat.mul_comm]
        _ ≤ ∑ z ∈ Finset.univ.erase zC, ∑ i : Fin t, blkCost C z i :=
            sum_le_sum (fun z hz => sum_le_sum (fun i _ =>
              hnocheat_ne hch z (mem_erase.mp hz).1 i))
    have hzC_sum : 2 * t + (missing X zC).card ≤ ∑ i : Fin t, blkCost C zC i := by
      have hterm : ∀ i : Fin t,
          (2 + if (zC, i, false) ∉ X ∧ (zC, i, true) ∉ X then 1 else 0) ≤ blkCost C zC i := by
        intro i
        split_ifs with hm
        · have hs : vS zC i ∈ C := (hpins (zC, i, false) hm.1).mpr rfl
          have ht : vT zC i ∉ C := by
            intro hmem
            have := (hpins (zC, i, true) hm.2).mp hmem
            simp [pinMap] at this
          exact hblk_pin zC i hs ht
        · exact hblk2 zC i
      calc 2 * t + (missing X zC).card
          = ∑ i : Fin t, (2 + if (zC, i, false) ∉ X ∧ (zC, i, true) ∉ X then 1 else 0) := by
            rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]
            congr 1
            rw [← card_filter]
            rfl
        _ ≤ ∑ i : Fin t, blkCost C zC i := sum_le_sum (fun i _ => hterm i)
    have hpow : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have harith : (3 * 2 ^ d - 1) * t = 2 * t + (2 ^ d - 1) * (3 * t) := by
      zify [hpow, show 1 ≤ 3 * 2 ^ d by omega]; ring
    omega

end Graph

end PEqualNP.Outside.L_lib_1516

theorem PEqualNP.Outside.L_lib_1516 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let cover := fun {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
let opt := fun {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (C : Finset (Fin N)) =>
  cover G C ∧ ∀ B, cover G B → C.sum w ≤ B.sum w
let bip := fun {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
let view := fun {k N : Nat} (p : Fin k → Fin N) (C : Finset (Fin N)) =>
  Finset.univ.filter (fun i => p i ∈ C)
let pins := fun {n : Nat} (Q : Finset (Fin n × Bool)) (C : Finset (Fin n)) =>
  ∀ a ∈ Q, decide (a.1 ∈ C)=a.2
∀ (d t r : Nat), r<t →
let Z := Fin (2^d)
let V := Z × (Fin t × Bool)
let ok := fun (X : Finset V) => ∃ z : Z,
  (Finset.univ.filter (fun i : Fin t => (z,i,false) ∉ X ∧ (z,i,true) ∉ X)).card ≤ r
let words := Finset.univ.filter (fun F : Z → Finset (Fin t) => ∀ z, (F z).card=r+1)
let prime := words.image (fun F => Finset.univ.filter (fun v : V => v.2.1 ∈ F v.1))
let represents := fun (H : Finset (Finset V)) => ∀ X, ok X ↔ ∀ C ∈ H, (C ∩ X).Nonempty
represents prime ∧ prime.card=(t.choose (r+1))^(2^d) ∧
  (∀ C ∈ prime, C.card=2*(r+1)*2^d) ∧
  (∀ H, represents H → prime ⊆ H) ∧
  ∃ (n : Nat) (G : Finset (Fin n × Fin n)) (w : Fin n → Nat)
    (p : V → Fin n × Bool) (D S C0 : Finset (Fin n)), Function.Injective (fun v => (p v).1) ∧
    (∀ e ∈ G, e.1<e.2) ∧ (∀ v, 0<w v) ∧ D.card=d ∧ bip G D S ∧ opt G w C0 ∧
    ∀ (X : Finset V) (b : Nat),
      (∃ C, cover G C ∧ pins ((Finset.univ \ X).image p) C ∧ C.sum w ≤ C0.sum w+b) ↔
      ∃ z : Z, (Finset.univ.filter (fun i : Fin t => (z,i,false) ∉ X ∧ (z,i,true) ∉ X)).card ≤ b) := by
  let : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  dsimp only
  intro d t r _
  have hmiss : ∀ (X : Finset (Fin (2 ^ d) × (Fin t × Bool))) (z : Fin (2 ^ d)),
      Finset.univ.filter (fun i : Fin t => (z, i, false) ∉ X ∧ (z, i, true) ∉ X) =
      PEqualNP.Outside.L_lib_1516.missing X z := by
    intro X z; ext i; simp [PEqualNP.Outside.L_lib_1516.missing]
  have hclause : ∀ F : Fin (2 ^ d) → Finset (Fin t),
      Finset.univ.filter (fun v : Fin (2 ^ d) × (Fin t × Bool) => v.2.1 ∈ F v.1) =
      PEqualNP.Outside.L_lib_1516.mkClause F := by
    intro F; ext v; simp [PEqualNP.Outside.L_lib_1516.mkClause]
  have hprime :
      (Finset.univ.filter (fun F : Fin (2 ^ d) → Finset (Fin t) => ∀ z, (F z).card = r + 1)).image
        (fun F => Finset.univ.filter (fun v : Fin (2 ^ d) × (Fin t × Bool) => v.2.1 ∈ F v.1)) =
      PEqualNP.Outside.L_lib_1516.primeSet d t r := by
    ext C
    simp only [PEqualNP.Outside.L_lib_1516.primeSet, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact ⟨F, hF, (hclause F).symm⟩
    · rintro ⟨F, hF, rfl⟩
      exact ⟨F, hF, hclause F⟩
  have hinter : ∀ (C X : Finset (Fin (2 ^ d) × (Fin t × Bool))),
      C ∩ X = PEqualNP.Outside.L_lib_1516.interSet C X := by
    intro C X; ext v; simp [PEqualNP.Outside.L_lib_1516.interSet]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X
    simp only [hmiss, hprime, hinter]
    exact PEqualNP.Outside.L_lib_1516.prime_represents X
  · rw [hprime]
    exact PEqualNP.Outside.L_lib_1516.primeSet_card d t r
  · rw [hprime]
    exact PEqualNP.Outside.L_lib_1516.primeSet_elem_card d t r
  · rw [hprime]
    intro H hH
    apply PEqualNP.Outside.L_lib_1516.prime_subset H
    intro X
    have h := hH X
    simp only [hmiss, hinter] at h
    exact h
  · let z0 : Fin (2 ^ d) := ⟨0, Nat.two_pow_pos d⟩
    let C0 := PEqualNP.Outside.L_lib_1516.baseCover d t z0 Finset.univ
    have hC0sum : C0.sum (PEqualNP.Outside.L_lib_1516.wt d t) =
        2 * d * PEqualNP.Outside.L_lib_1516.Wbig d t + (3 * 2 ^ d - 1) * t := by
      have h := PEqualNP.Outside.L_lib_1516.baseCover_sum z0 (Finset.univ : Finset (Fin (2 ^ d) × (Fin t × Bool)))
      have h0 : (PEqualNP.Outside.L_lib_1516.missing (Finset.univ : Finset (Fin (2 ^ d) × (Fin t × Bool))) z0).card = 0 := by
        simp [PEqualNP.Outside.L_lib_1516.missing]
      simpa [C0, h0] using h
    refine ⟨PEqualNP.Outside.L_lib_1516.nVert d t,
      PEqualNP.Outside.L_lib_1516.Ggraph d t,
      PEqualNP.Outside.L_lib_1516.wt d t,
      PEqualNP.Outside.L_lib_1516.pinMap d t,
      PEqualNP.Outside.L_lib_1516.Dset d t,
      PEqualNP.Outside.L_lib_1516.Sset d t,
      C0,
      PEqualNP.Outside.L_lib_1516.pinMap_inj d t,
      PEqualNP.Outside.L_lib_1516.Ggraph_lt d t,
      PEqualNP.Outside.L_lib_1516.wt_pos d t,
      PEqualNP.Outside.L_lib_1516.Dset_card d t,
      PEqualNP.Outside.L_lib_1516.Ggraph_bip d t,
      ⟨PEqualNP.Outside.L_lib_1516.baseCover_covers z0 Finset.univ, fun B hB => by
        rw [hC0sum]
        exact (PEqualNP.Outside.L_lib_1516.cover_lower B hB).2.2.1⟩,
      ?_⟩
    intro X b
    simp only [hmiss]
    constructor
    · rintro ⟨C, hcov, hpins, hle⟩
      rw [hC0sum] at hle
      have hpins' : ∀ v : Fin (2 ^ d) × (Fin t × Bool), v ∉ X →
          ((PEqualNP.Outside.L_lib_1516.pinMap d t v).1 ∈ C ↔
            (PEqualNP.Outside.L_lib_1516.pinMap d t v).2 = true) := by
        intro v hv
        have ha := Finset.mem_image_of_mem (PEqualNP.Outside.L_lib_1516.pinMap d t)
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩)
        have h := hpins (PEqualNP.Outside.L_lib_1516.pinMap d t v) ha
        cases hb : (PEqualNP.Outside.L_lib_1516.pinMap d t v).2
        · rw [hb] at h
          simp [decide_eq_false_iff_not.mp h]
        · rw [hb] at h
          simp [decide_eq_true_eq.mp h]
      exact (PEqualNP.Outside.L_lib_1516.cover_lower C hcov).2.2.2 X b hpins' hle
    · rintro ⟨z, hz⟩
      refine ⟨PEqualNP.Outside.L_lib_1516.baseCover d t z X,
        PEqualNP.Outside.L_lib_1516.baseCover_covers z X,
        ?_, ?_⟩
      · intro a ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
        have h := PEqualNP.Outside.L_lib_1516.baseCover_pins z X v (Finset.mem_sdiff.mp hv).2
        cases hb : (PEqualNP.Outside.L_lib_1516.pinMap d t v).2
        · rw [hb] at h
          exact decide_eq_false (by simpa using h)
        · rw [hb] at h
          exact decide_eq_true (by simpa using h)
      · rw [hC0sum, PEqualNP.Outside.L_lib_1516.baseCover_sum z X]
        exact Nat.add_le_add_left hz _
