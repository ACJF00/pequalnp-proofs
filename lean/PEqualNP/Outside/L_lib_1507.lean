import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_lib_1507

section Construction

variable {k d : ℕ} (F : Finset (Fin d) → List ((Option (Fin k) × Option (Fin k)) × ℕ))

private abbrev PosIdx (Z : Finset (Fin d)) :=
  { idx : Fin (F Z).length // 0 < ((F Z)[idx.val]).2 }

private abbrev V :=
  Fin d ⊕ (Fin d × Bool) ⊕ (Fin k × Bool) ⊕ Bool ⊕ Finset (Fin d) ⊕
    ((Z : Finset (Fin d)) × (PosIdx F Z × Fin 3))

private def vSel (j : Fin d) : V F := Sum.inl j
private def vMir (j : Fin d) (b : Bool) : V F := Sum.inr (Sum.inl (j, b))
private def vRaw (i : Fin k) (b : Bool) : V F := Sum.inr (Sum.inr (Sum.inl (i, b)))
private def vAnc (b : Bool) : V F := Sum.inr (Sum.inr (Sum.inr (Sum.inl b)))
private def vBon (Z : Finset (Fin d)) : V F := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl Z))))
private def vHlp (Z : Finset (Fin d)) (idx : PosIdx F Z) (r : Fin 3) : V F :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨Z, (idx, r)⟩))))

private def isSide : V F → Bool
  | Sum.inl _ => false
  | Sum.inr (Sum.inl (_, b)) => !b
  | Sum.inr (Sum.inr (Sum.inl (_, b))) => !b
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl b))) => !b
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => true
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨_, (_, r)⟩)))) => decide (r = 1)

private def isSel : V F → Prop
  | Sum.inl _ => True
  | _ => False

private def isHeavy : V F → Prop
  | Sum.inl _ => True
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr (Sum.inl _)) => True
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => True
  | _ => False

private def srcV (c : Option (Fin k) × Option (Fin k)) : V F :=
  c.1.elim (vAnc F false) (fun i => vRaw F i false)

private def tgtV (c : Option (Fin k) × Option (Fin k)) : V F :=
  c.2.elim (vAnc F true) (fun j => vRaw F j true)

private def dirAdj : V F → V F → Prop
  | u, v =>
    (∃ j b, u = vSel F j ∧ v = vMir F j b) ∨
    (∃ i, u = vRaw F i false ∧ v = vRaw F i true) ∨
    (∃ Z j, j ∈ Z ∧ u = vSel F j ∧ v = vBon F Z) ∨
    (∃ Z j, j ∉ Z ∧ u = vMir F j true ∧ v = vBon F Z) ∨
    (∃ Z idx r j, j ∈ Z ∧ u = vSel F j ∧ v = vHlp F Z idx r) ∨
    (∃ Z idx r j, j ∉ Z ∧ u = vMir F j (decide (r = 1)) ∧ v = vHlp F Z idx r) ∨
    (∃ Z idx, u = srcV F ((F Z)[idx.1.val]).1 ∧ v = vHlp F Z idx 0) ∨
    (∃ Z idx, u = vHlp F Z idx 0 ∧ v = vHlp F Z idx 1) ∨
    (∃ Z idx, u = vHlp F Z idx 1 ∧ v = tgtV F ((F Z)[idx.1.val]).1) ∨
    (∃ Z idx j, ((F Z)[idx.1.val]).1.2 = some j ∧ u = vRaw F j false ∧ v = vHlp F Z idx 2)

private def adj (u v : V F) : Prop := dirAdj F u v ∨ dirAdj F v u

private lemma dirAdj_ne {u v : V F} (h : dirAdj F u v) : u ≠ v := by
  rcases h with ⟨j, b, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨Z, j, _, rfl, rfl⟩ |
    ⟨Z, j, _, rfl, rfl⟩ | ⟨Z, idx, r, j, _, rfl, rfl⟩ | ⟨Z, idx, r, j, _, rfl, rfl⟩ |
    ⟨Z, idx, rfl, rfl⟩ | ⟨Z, idx, rfl, rfl⟩ | ⟨Z, idx, rfl, rfl⟩ | ⟨Z, idx, j, _, rfl, rfl⟩
  all_goals
    try (intro heq; cases heq)
  · unfold srcV; cases ((F Z)[idx.1.val]).1.1 <;> intro heq <;> cases heq
  · unfold tgtV; cases ((F Z)[idx.1.val]).1.2 <;> intro heq <;> cases heq

private lemma adj_ne {u v : V F} (h : adj F u v) : u ≠ v := by
  rcases h with h | h
  · exact dirAdj_ne F h
  · exact (dirAdj_ne F h).symm

private lemma dirAdj_bip {u v : V F} (h : dirAdj F u v) (hu : ¬ isSel F u) (hv : ¬ isSel F v) :
    isSide F u ≠ isSide F v := by
  rcases h with ⟨j, b, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨Z, j, _, rfl, rfl⟩ |
    ⟨Z, j, _, rfl, rfl⟩ | ⟨Z, idx, r, j, _, rfl, rfl⟩ | ⟨Z, idx, r, j, _, rfl, rfl⟩ |
    ⟨Z, idx, rfl, rfl⟩ | ⟨Z, idx, rfl, rfl⟩ | ⟨Z, idx, rfl, rfl⟩ | ⟨Z, idx, j, _, rfl, rfl⟩
  · exact absurd trivial hu
  · simp [isSide, vRaw]
  · exact absurd trivial hu
  · simp [isSide, vMir, vBon]
  · exact absurd trivial hu
  · fin_cases r <;> simp [isSide, vMir, vHlp]
  · unfold srcV; cases ((F Z)[idx.1.val]).1.1 <;> simp [isSide, vAnc, vRaw, vHlp]
  · simp [isSide, vHlp]
  · unfold tgtV; cases ((F Z)[idx.1.val]).1.2 <;> simp [isSide, vAnc, vRaw, vHlp]
  · simp [isSide, vRaw, vHlp]

private lemma adj_bip {u v : V F} (h : adj F u v) (hu : ¬ isSel F u) (hv : ¬ isSel F v) :
    isSide F u ≠ isSide F v := by
  rcases h with h | h
  · exact dirAdj_bip F h hu hv
  · exact (dirAdj_bip F h hv hu).symm

private def clauseW (Z : Finset (Fin d)) : ℕ := ((F Z).map Prod.snd).sum

private def Mval : ℕ := (Finset.univ.sup (fun Z : Finset (Fin d) => 2 * clauseW F Z)) + 1

private def lightW : V F → ℕ
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl Z)))) => Mval F - 2 * clauseW F Z
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨Z, (idx, r)⟩)))) =>
      if r = 1 then 2 * ((F Z)[idx.1.val]).2 else ((F Z)[idx.1.val]).2
  | _ => 0

open scoped Classical in
private noncomputable def Hval : ℕ := Finset.univ.sum (lightW F) + 1

open scoped Classical in
private noncomputable def wtV : V F → ℕ
  | Sum.inl _ => 2 * Hval F
  | Sum.inr (Sum.inl _) => Hval F
  | Sum.inr (Sum.inr (Sum.inl _)) => Hval F
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => Hval F
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl Z)))) => Mval F - 2 * clauseW F Z
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨Z, (idx, r)⟩)))) =>
      if r = 1 then 2 * ((F Z)[idx.1.val]).2 else ((F Z)[idx.1.val]).2

open scoped Classical in
private lemma wtV_pos (v : V F) : 0 < wtV F v := by
  rcases v with j | ⟨j, b⟩ | ⟨i, b⟩ | b | Z | ⟨Z, idx, r⟩
  · simp only [wtV, Hval]; omega
  · simp only [wtV, Hval]; omega
  · simp only [wtV, Hval]; omega
  · simp only [wtV, Hval]; omega
  · simp only [wtV, Mval]
    have hle : 2 * clauseW F Z ≤ Finset.univ.sup (fun Z' : Finset (Fin d) => 2 * clauseW F Z') :=
      Finset.le_sup (f := fun Z' : Finset (Fin d) => 2 * clauseW F Z') (Finset.mem_univ Z)
    omega
  · simp only [wtV]
    have hpos := idx.2
    split_ifs <;> omega

open scoped Classical in
private lemma wtV_light (v : V F) (hv : ¬ isHeavy F v) : wtV F v = lightW F v := by
  rcases v with _ | _ | _ | _ | _ | _
  · exact absurd trivial hv
  · exact absurd trivial hv
  · exact absurd trivial hv
  · exact absurd trivial hv
  · rfl
  · rfl

private lemma list_sum_fin_eq {α : Type*} (L : List α) (g : α → ℕ) :
    (L.map g).sum = Finset.univ.sum (fun i : Fin L.length => g (L[i.val])) := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Fin.sum_univ_succ,
      Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ, ih]

private lemma sum_posIdx_eq (Z : Finset (Fin d)) (g : Fin (F Z).length → ℕ)
    (hg0 : ∀ idx : Fin (F Z).length, ((F Z)[idx.val]).2 = 0 → g idx = 0) :
    Finset.univ.sum (fun idx : PosIdx F Z => g idx.1) = Finset.univ.sum g := by
  have h1 : Finset.univ.sum (fun idx : PosIdx F Z => g idx.1) =
      (Finset.univ.filter (fun idx : Fin (F Z).length => 0 < ((F Z)[idx.val]).2)).sum g := by
    refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
    · intro x _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩
    · intro x1 _ x2 _ h; exact Subtype.ext h
    · intro idx hidx; exact ⟨⟨idx, (Finset.mem_filter.mp hidx).2⟩, Finset.mem_univ _, rfl⟩
    · intro x _; rfl
  rw [h1, Finset.sum_filter]
  refine Finset.sum_congr rfl fun idx _ => ?_
  by_cases h : 0 < ((F Z)[idx.val]).2
  · simp [h]
  · simp [h, hg0 idx (by omega)]

open scoped Classical in
private lemma card_V_le :
    Fintype.card (V F) ≤ 5 * d + 2 * k + 2 + 3 * Finset.univ.sum (fun Z => (F Z).length) + 2 ^ d := by
  simp only [V, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_sigma, Fintype.card_finset]
  have hhlp : ∑ Z : Finset (Fin d), Fintype.card (PosIdx F Z) * 3 ≤
      3 * ∑ Z : Finset (Fin d), (F Z).length := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun Z _ => ?_
    have hle : Fintype.card (PosIdx F Z) ≤ (F Z).length := by
      calc Fintype.card (PosIdx F Z) ≤ Fintype.card (Fin (F Z).length) := Fintype.card_subtype_le _
        _ = (F Z).length := Fintype.card_fin _
    omega
  omega

private def isIndep (I : Finset (V F)) : Prop := ∀ u v, adj F u v → u ∈ I → v ∉ I

open scoped Classical in
private noncomputable def idealI (Z : Finset (Fin d)) (X : Finset (Fin k)) : Finset (V F) :=
  Finset.univ.filter fun u =>
    match u with
    | Sum.inl j => j ∉ Z
    | Sum.inr (Sum.inl (j, _)) => j ∈ Z
    | Sum.inr (Sum.inr (Sum.inl (i, false))) => i ∈ X
    | Sum.inr (Sum.inr (Sum.inl (i, true))) => i ∉ X
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => True
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl Z0)))) => Z0 = Z
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨Z0, (idx, r)⟩)))) =>
        Z0 = Z ∧
        let c := ((F Z0)[idx.1.val]).1
        let uT := c.1.elim True (fun i => i ∈ X)
        let vT := c.2.elim True (fun j => j ∉ X)
        if r = 0 then ¬ uT ∧ vT
        else if r = 1 then ¬ vT
        else vT

open scoped Classical in
private noncomputable def reqHeavy (Z : Finset (Fin d)) (X : Finset (Fin k)) : Finset (V F) :=
  Finset.univ.filter fun u =>
    match u with
    | Sum.inl j => j ∉ Z
    | Sum.inr (Sum.inl (j, _)) => j ∈ Z
    | Sum.inr (Sum.inr (Sum.inl (i, false))) => i ∈ X
    | Sum.inr (Sum.inr (Sum.inl (i, true))) => i ∉ X
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => True
    | _ => False

open scoped Classical in
private lemma idealI_indep (Z : Finset (Fin d)) (X : Finset (Fin k)) :
    isIndep F (idealI F Z X) := by
  intro u v huv hu hv
  have hdir : ∀ u v, dirAdj F u v → u ∈ idealI F Z X → v ∈ idealI F Z X → False := by
    intro u v h hu hv
    rcases h with ⟨j, b, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨Z0, j, hjZ0, rfl, rfl⟩ |
      ⟨Z0, j, hjZ0, rfl, rfl⟩ | ⟨Z0, idx, r, j, hjZ0, rfl, rfl⟩ | ⟨Z0, idx, r, j, hjZ0, rfl, rfl⟩ |
      ⟨Z0, idx, rfl, rfl⟩ | ⟨Z0, idx, rfl, rfl⟩ | ⟨Z0, idx, rfl, rfl⟩ | ⟨Z0, idx, j, htj, rfl, rfl⟩
    · simp [idealI, vSel, vMir] at hu hv; exact hu hv
    · simp [idealI, vRaw] at hu hv; exact hv hu
    · simp [idealI, vSel, vBon] at hu hv; rw [hv] at hjZ0; exact hu hjZ0
    · simp [idealI, vMir, vBon] at hu hv; rw [hv] at hjZ0; exact hjZ0 hu
    · simp [idealI, vSel, vHlp] at hu hv; rw [hv.1] at hjZ0; exact hu hjZ0
    · simp [idealI, vMir, vHlp] at hu hv; rw [hv.1] at hjZ0; exact hjZ0 hu
    · simp only [idealI, vHlp, Finset.mem_filter, Finset.mem_univ, true_and, ↓reduceIte] at hv
      cases hsrc : ((F Z0)[idx.1.val]).1.1 with
      | none => simp [hsrc] at hv
      | some i =>
        simp only [srcV, hsrc, Option.elim_some, idealI, vRaw, Finset.mem_filter,
          Finset.mem_univ, true_and] at hu
        simp [hsrc] at hv
        exact hv.2.1 hu
    · simp only [idealI, vHlp, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      have h10 : (1 : Fin 3) ≠ 0 := by decide
      simp only [↓reduceIte, h10] at hu hv
      exact hv.2 hu.2.2
    · simp only [idealI, vHlp, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      have h10 : (1 : Fin 3) ≠ 0 := by decide
      simp only [h10, ↓reduceIte] at hu
      cases htgt : ((F Z0)[idx.1.val]).1.2 with
      | none => simp [htgt] at hu
      | some j =>
        simp only [tgtV, htgt, Option.elim_some, idealI, vRaw, Finset.mem_filter,
          Finset.mem_univ, true_and] at hv
        simp [htgt] at hu
        exact hv hu.2
    · simp only [idealI, vRaw, vHlp, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      have h21 : (2 : Fin 3) ≠ 1 := by decide
      simp only [h20, h21, ↓reduceIte, htj, Option.elim_some] at hv
      exact hv.2 hu
  rcases huv with h | h
  · exact hdir u v h hu hv
  · exact hdir v u h hv hu

open scoped Classical in
private lemma reqHeavy_sum (Z : Finset (Fin d)) (X : Finset (Fin k)) :
    (reqHeavy F Z X).sum (wtV F) = (2 * d + k + 2) * Hval F := by
  rw [reqHeavy, Finset.sum_filter]
  simp only [V, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, wtV,
    ↓reduceIte, Finset.sum_const_zero, add_zero]
  have hrearr : ∀ (a b c e : ℕ), a + (b + (c + e)) = (a + b) + c + e := fun _ _ _ _ => by omega
  rw [hrearr]
  have hd' : ∀ (d1 : ∀ x : Fin d, Decidable (x ∉ Z)) (d2 d3 : ∀ x : Fin d, Decidable (x ∈ Z)),
      (∑ x : Fin d, @ite ℕ (x ∉ Z) (d1 x) (2 * Hval F) 0) +
      ∑ x : Fin d, ((@ite ℕ (x ∈ Z) (d2 x) (Hval F) 0) + (@ite ℕ (x ∈ Z) (d3 x) (Hval F) 0)) =
      2 * d * Hval F := fun _ _ _ => by
    rw [← Finset.sum_add_distrib]
    trans ∑ _x : Fin d, (2 * Hval F)
    · refine Finset.sum_congr rfl fun x _ => by by_cases hx : x ∈ Z <;> simp [hx] <;> omega
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      rw [← Nat.mul_assoc, Nat.mul_comm d 2]
  rw [hd']
  trans (2 * d * Hval F + k * Hval F + (Hval F + Hval F))
  · congr 2
    trans ∑ _x : Fin k, Hval F
    · refine Finset.sum_congr rfl fun x _ => by by_cases hx : x ∈ X <;> simp [hx]
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  · simp only [Nat.add_mul, Nat.mul_assoc]; omega

open scoped Classical in
private lemma heavy_props (Z : Finset (Fin d)) (X : Finset (Fin k)) (I : Finset (V F))
    (hI : isIndep F I)
    (hsel : ∀ j : Fin d, vSel F j ∈ I ↔ j ∉ Z)
    (hraw : ∀ i : Fin k, vRaw F i true ∈ I ↔ i ∉ X) :
    (I.filter (isHeavy F) ⊆ reqHeavy F Z X) ∧
    (∀ v ∈ reqHeavy F Z X, v ∉ I →
      (I.filter (isHeavy F)).sum (wtV F) + Hval F ≤ (2 * d + k + 2) * Hval F) := by
  have hsub : I.filter (isHeavy F) ⊆ reqHeavy F Z X := by
    intro u hu
    rcases Finset.mem_filter.mp hu with ⟨huI, huH⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
    rcases u with j | ⟨j, b⟩ | ⟨i, b⟩ | b | _ | _
    · exact (hsel j).mp huI
    · by_contra hjZ
      exact hI (vSel F j) (vMir F j b) (Or.inl (Or.inl ⟨j, b, rfl, rfl⟩)) ((hsel j).mpr hjZ) huI
    · cases b
      · by_contra hiX
        exact hI (vRaw F i false) (vRaw F i true) (Or.inl (Or.inr (Or.inl ⟨i, rfl, rfl⟩))) huI ((hraw i).mpr hiX)
      · exact (hraw i).mp huI
    · trivial
    · exact absurd huH id
    · exact absurd huH id
  refine ⟨hsub, fun v hv hvI => ?_⟩
  have hv_not : v ∉ I.filter (isHeavy F) := fun h => hvI (Finset.mem_filter.mp h).1
  have hsub_er : I.filter (isHeavy F) ⊆ (reqHeavy F Z X).erase v := fun u hu =>
    Finset.mem_erase.mpr ⟨fun h => hv_not (h ▸ hu), hsub hu⟩
  have hle1 : (I.filter (isHeavy F)).sum (wtV F) + wtV F v ≤ (reqHeavy F Z X).sum (wtV F) := by
    calc (I.filter (isHeavy F)).sum (wtV F) + wtV F v
        ≤ ((reqHeavy F Z X).erase v).sum (wtV F) + wtV F v :=
          Nat.add_le_add_right (Finset.sum_le_sum_of_subset hsub_er) _
      _ = (reqHeavy F Z X).sum (wtV F) := Finset.sum_erase_add _ _ hv
  have hv_ge : Hval F ≤ wtV F v := by
    rcases v with _ | _ | _ | _ | _ | _
    · simp only [wtV]; omega
    · simp only [wtV]; omega
    · simp only [wtV]; omega
    · simp only [wtV]; omega
    · simp [reqHeavy] at hv
    · simp [reqHeavy] at hv
  rw [reqHeavy_sum F Z X] at hle1
  omega

open scoped Classical in
private noncomputable def lossFn (Z : Finset (Fin d)) (X : Finset (Fin k)) : ℕ :=
  ((F Z).map (fun c =>
    if c.1.1.elim True (fun i => i ∈ X) ∧ c.1.2.elim True (fun j => j ∉ X)
    then c.2 else 0)).sum

open scoped Classical in
private lemma light_sum_decomp (Z : Finset (Fin d)) (I : Finset (V F))
    (hbon_ne : ∀ Z0 : Finset (Fin d), Z0 ≠ Z → vBon F Z0 ∉ I)
    (hhlp_ne : ∀ Z0 (idx : PosIdx F Z0) (r : Fin 3), Z0 ≠ Z → vHlp F Z0 idx r ∉ I) :
    (I.filter (fun u => ¬ isHeavy F u)).sum (wtV F) =
      (if vBon F Z ∈ I then Mval F - 2 * clauseW F Z else 0) +
      Finset.univ.sum (fun idx : PosIdx F Z =>
        (if vHlp F Z idx 0 ∈ I then ((F Z)[idx.1.val]).2 else 0) +
        (if vHlp F Z idx 1 ∈ I then 2 * ((F Z)[idx.1.val]).2 else 0) +
        (if vHlp F Z idx 2 ∈ I then ((F Z)[idx.1.val]).2 else 0)) := by
  have h1 : (I.filter (fun u => ¬ isHeavy F u)).sum (wtV F) =
      ∑ u : V F, (if u ∈ I ∧ ¬ isHeavy F u then wtV F u else 0) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext u; simp
  rw [h1]
  simp only [V, Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_prod_type,
    isHeavy, not_true_eq_false, and_false, ↓reduceIte, Finset.sum_const_zero, zero_add]
  congr 1
  · rw [Finset.sum_eq_single Z]
    · by_cases hb : vBon F Z ∈ I
      · have hb' : Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl Z)))) ∈ I := hb
        simp [vBon, wtV, hb']
      · have hb' : Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl Z)))) ∉ I := hb
        simp [vBon, wtV, hb']
    · intro Z0 _ hne; have h := hbon_ne Z0 hne; simp only [vBon] at h; simp [h]
    · intro h; exact absurd (Finset.mem_univ Z) h
  · rw [Finset.sum_eq_single Z]
    · refine Finset.sum_congr rfl fun idx _ => ?_
      rw [Fin.sum_univ_three]
      by_cases h0 : vHlp F Z idx 0 ∈ I <;>
        by_cases h1 : vHlp F Z idx 1 ∈ I <;>
        by_cases h2 : vHlp F Z idx 2 ∈ I
      all_goals
        simp only [vHlp] at h0 h1 h2
        simp [vHlp, wtV, h0, h1, h2]
    · intro Z0 _ hne
      refine Finset.sum_eq_zero fun idx _ => Finset.sum_eq_zero fun r _ => ?_
      have h := hhlp_ne Z0 idx r hne; simp only [vHlp] at h; simp [h]
    · intro h; exact absurd (Finset.mem_univ Z) h

open scoped Classical in
private lemma light_bound (Z : Finset (Fin d)) (X : Finset (Fin k)) (I : Finset (V F))
    (hI : isIndep F I)
    (hsel : ∀ j : Fin d, vSel F j ∈ I ↔ j ∉ Z)
    (hmir : ∀ j : Fin d, ∀ b : Bool, j ∈ Z → vMir F j b ∈ I)
    (hrawT : ∀ i : Fin k, vRaw F i true ∈ I ↔ i ∉ X)
    (hrawF : ∀ i : Fin k, i ∈ X → vRaw F i false ∈ I)
    (hanc : vAnc F false ∈ I ∧ vAnc F true ∈ I) :
    (I.filter (fun u => ¬ isHeavy F u)).sum (wtV F) + lossFn F Z X ≤ Mval F ∧
    ((I.filter (fun u => ¬ isHeavy F u)).sum (wtV F) + lossFn F Z X = Mval F →
      I.filter (fun u => ¬ isHeavy F u) = (idealI F Z X).filter (fun u => ¬ isHeavy F u)) := by
  have hbon_ne : ∀ Z0 : Finset (Fin d), Z0 ≠ Z → vBon F Z0 ∉ I := by
    intro Z0 hne hmem
    have hdiff : (∃ j, j ∈ Z0 ∧ j ∉ Z) ∨ (∃ j, j ∈ Z ∧ j ∉ Z0) := by
      by_contra h
      apply hne; ext j
      exact ⟨fun hj => by_contra fun hjZ => h (Or.inl ⟨j, hj, hjZ⟩),
             fun hj => by_contra fun hj0 => h (Or.inr ⟨j, hj, hj0⟩)⟩
    rcases hdiff with ⟨j, hj0, hjZ⟩ | ⟨j, hjZ, hj0⟩
    · exact hI (vSel F j) (vBon F Z0) (Or.inl (Or.inr (Or.inr (Or.inl ⟨Z0, j, hj0, rfl, rfl⟩))))
        ((hsel j).mpr hjZ) hmem
    · exact hI (vMir F j true) (vBon F Z0)
        (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z0, j, hj0, rfl, rfl⟩)))))
        (hmir j true hjZ) hmem
  have hhlp_ne : ∀ Z0 (idx : PosIdx F Z0) (r : Fin 3), Z0 ≠ Z → vHlp F Z0 idx r ∉ I := by
    intro Z0 idx r hne hmem
    have hdiff : (∃ j, j ∈ Z0 ∧ j ∉ Z) ∨ (∃ j, j ∈ Z ∧ j ∉ Z0) := by
      by_contra h
      apply hne; ext j
      exact ⟨fun hj => by_contra fun hjZ => h (Or.inl ⟨j, hj, hjZ⟩),
             fun hj => by_contra fun hj0 => h (Or.inr ⟨j, hj, hj0⟩)⟩
    rcases hdiff with ⟨j, hj0, hjZ⟩ | ⟨j, hjZ, hj0⟩
    · exact hI (vSel F j) (vHlp F Z0 idx r)
        (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z0, idx, r, j, hj0, rfl, rfl⟩))))))
        ((hsel j).mpr hjZ) hmem
    · exact hI (vMir F j (decide (r = 1))) (vHlp F Z0 idx r)
        (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z0, idx, r, j, hj0, rfl, rfl⟩)))))))
        (hmir j (decide (r = 1)) hjZ) hmem
  let cGain (idx : PosIdx F Z) : ℕ :=
    (if vHlp F Z idx 0 ∈ I then ((F Z)[idx.1.val]).2 else 0) +
    (if vHlp F Z idx 1 ∈ I then 2 * ((F Z)[idx.1.val]).2 else 0) +
    (if vHlp F Z idx 2 ∈ I then ((F Z)[idx.1.val]).2 else 0)
  let cLoss (idx : PosIdx F Z) : ℕ :=
    let c := ((F Z)[idx.1.val]).1
    if c.1.elim True (fun i => i ∈ X) ∧ c.2.elim True (fun j => j ∉ X) then ((F Z)[idx.1.val]).2 else 0
  have hclause : ∀ idx : PosIdx F Z,
      cGain idx + cLoss idx ≤ 2 * ((F Z)[idx.1.val]).2 ∧
      (cGain idx + cLoss idx = 2 * ((F Z)[idx.1.val]).2 →
        ∀ r : Fin 3, vHlp F Z idx r ∈ I ↔ vHlp F Z idx r ∈ idealI F Z X) := by
    intro idx
    have hwc : 0 < ((F Z)[idx.1.val]).2 := idx.2
    have hu_in : ((F Z)[idx.1.val]).1.1.elim True (fun i => i ∈ X) → srcV F ((F Z)[idx.1.val]).1 ∈ I := by
      unfold srcV
      cases hc1 : ((F Z)[idx.1.val]).1.1 with
      | none => intro _; exact hanc.1
      | some i => intro hi; exact hrawF i hi
    have hv_in : ((F Z)[idx.1.val]).1.2.elim True (fun j => j ∉ X) → tgtV F ((F Z)[idx.1.val]).1 ∈ I := by
      unfold tgtV
      cases hc2 : ((F Z)[idx.1.val]).1.2 with
      | none => intro _; exact hanc.2
      | some j => intro hj; exact (hrawT j).mpr hj
    have hab : ¬ (vHlp F Z idx 0 ∈ I ∧ vHlp F Z idx 1 ∈ I) := by
      rintro ⟨h0, h1⟩
      exact hI _ _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z, idx, rfl, rfl⟩))))))))) h0 h1
    have ha_blk : ((F Z)[idx.1.val]).1.1.elim True (fun i => i ∈ X) → vHlp F Z idx 0 ∉ I := by
      intro hu h0
      exact hI _ _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z, idx, rfl, rfl⟩)))))))) (hu_in hu) h0
    have hb_blk : ((F Z)[idx.1.val]).1.2.elim True (fun j => j ∉ X) → vHlp F Z idx 1 ∉ I := by
      intro hv h1
      exact hI _ _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Z, idx, rfl, rfl⟩)))))))))) h1 (hv_in hv)
    have hd_blk : ¬ ((F Z)[idx.1.val]).1.2.elim True (fun j => j ∉ X) → vHlp F Z idx 2 ∉ I := by
      intro hnv h2
      cases hc2 : ((F Z)[idx.1.val]).1.2 with
      | none => simp [hc2] at hnv
      | some j =>
        simp only [hc2, Option.elim_some, not_not] at hnv
        exact hI _ _ (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Z, idx, j, hc2, rfl, rfl⟩)))))))))) (hrawF j hnv) h2
    by_cases huT : ((F Z)[idx.1.val]).1.1.elim True (fun i => i ∈ X) <;>
      by_cases hvT : ((F Z)[idx.1.val]).1.2.elim True (fun j => j ∉ X)
    · have h0 : vHlp F Z idx 0 ∉ I := ha_blk huT
      have h1 : vHlp F Z idx 1 ∉ I := hb_blk hvT
      constructor
      · simp only [cGain, cLoss, h0, h1, ↓reduceIte, huT, hvT, and_self]
        by_cases h2 : vHlp F Z idx 2 ∈ I <;> simp [h2] <;> omega
      · intro heq r
        have h2 : vHlp F Z idx 2 ∈ I := by
          by_contra h2
          simp only [cGain, cLoss, h0, h1, h2, ↓reduceIte, huT, hvT, and_self] at heq
          omega
        simp only [vHlp] at h0 h1 h2
        fin_cases r <;> simp [idealI, vHlp, h0, h1, h2, huT, hvT]
    · have h2 : vHlp F Z idx 2 ∉ I := hd_blk hvT
      constructor
      · simp only [cGain, cLoss, h2, ↓reduceIte, huT, hvT, and_false]
        by_cases h0 : vHlp F Z idx 0 ∈ I <;> by_cases h1 : vHlp F Z idx 1 ∈ I
        · exact absurd ⟨h0, h1⟩ hab
        · simp [h0, h1]; omega
        · simp [h0, h1]
        · simp [h0, h1]
      · intro heq r
        have h1 : vHlp F Z idx 1 ∈ I := by
          by_contra h1
          simp only [cGain, cLoss, h1, h2, ↓reduceIte, huT, hvT, and_false] at heq
          by_cases h0 : vHlp F Z idx 0 ∈ I <;> simp [h0] at heq <;> omega
        have h0 : vHlp F Z idx 0 ∉ I := fun h0 => hab ⟨h0, h1⟩
        simp only [vHlp] at h0 h1 h2
        fin_cases r <;> simp [idealI, vHlp, h0, h1, h2, huT, hvT]
    · have h1 : vHlp F Z idx 1 ∉ I := hb_blk hvT
      constructor
      · simp only [cGain, cLoss, h1, ↓reduceIte, huT, hvT, false_and]
        by_cases h0 : vHlp F Z idx 0 ∈ I <;> by_cases h2 : vHlp F Z idx 2 ∈ I <;>
          simp [h0, h2] <;> omega
      · intro heq r
        have h0 : vHlp F Z idx 0 ∈ I := by
          by_contra h0
          simp only [cGain, cLoss, h0, h1, ↓reduceIte, huT, hvT, false_and] at heq
          by_cases h2 : vHlp F Z idx 2 ∈ I <;> simp [h2] at heq <;> omega
        have h2 : vHlp F Z idx 2 ∈ I := by
          by_contra h2
          simp only [cGain, cLoss, h0, h1, h2, ↓reduceIte, huT, hvT, false_and] at heq
          omega
        simp only [vHlp] at h0 h1 h2
        fin_cases r <;> simp [idealI, vHlp, h0, h1, h2, huT, hvT]
    · have h2 : vHlp F Z idx 2 ∉ I := hd_blk hvT
      constructor
      · simp only [cGain, cLoss, h2, ↓reduceIte, huT, hvT, and_false]
        by_cases h0 : vHlp F Z idx 0 ∈ I <;> by_cases h1 : vHlp F Z idx 1 ∈ I
        · exact absurd ⟨h0, h1⟩ hab
        · simp [h0, h1]; omega
        · simp [h0, h1]
        · simp [h0, h1]
      · intro heq r
        have h1 : vHlp F Z idx 1 ∈ I := by
          by_contra h1
          simp only [cGain, cLoss, h1, h2, ↓reduceIte, huT, hvT, and_false] at heq
          by_cases h0 : vHlp F Z idx 0 ∈ I <;> simp [h0] at heq <;> omega
        have h0 : vHlp F Z idx 0 ∉ I := fun h0 => hab ⟨h0, h1⟩
        simp only [vHlp] at h0 h1 h2
        fin_cases r <;> simp [idealI, vHlp, h0, h1, h2, huT, hvT]
  have hclauseW_eq : clauseW F Z = Finset.univ.sum (fun idx : PosIdx F Z => ((F Z)[idx.1.val]).2) := by
    rw [clauseW, list_sum_fin_eq, ← sum_posIdx_eq F Z (fun i => ((F Z)[i.val]).2) (fun _ h => h)]
  have hloss_eq : lossFn F Z X = Finset.univ.sum cLoss := by
    rw [lossFn, list_sum_fin_eq, ← sum_posIdx_eq F Z (fun i =>
      if ((F Z)[i.val]).1.1.elim True (fun a => a ∈ X) ∧ ((F Z)[i.val]).1.2.elim True (fun b => b ∉ X)
      then ((F Z)[i.val]).2 else 0) (fun i h => by simp [h])]
  have hsum_le : Finset.univ.sum cGain + lossFn F Z X ≤ 2 * clauseW F Z := by
    rw [hloss_eq, hclauseW_eq, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun idx _ => (hclause idx).1
  have hM_ge : 2 * clauseW F Z < Mval F := by
    have hle := Finset.le_sup (f := fun Z' : Finset (Fin d) => 2 * clauseW F Z') (Finset.mem_univ Z)
    dsimp only [Mval]; omega
  rw [light_sum_decomp F Z I hbon_ne hhlp_ne]
  change (if vBon F Z ∈ I then Mval F - 2 * clauseW F Z else 0) + Finset.univ.sum cGain + lossFn F Z X ≤ Mval F ∧
    ((if vBon F Z ∈ I then Mval F - 2 * clauseW F Z else 0) + Finset.univ.sum cGain + lossFn F Z X = Mval F → _)
  constructor
  · by_cases hb : vBon F Z ∈ I <;> simp [hb] <;> omega
  · intro heq
    have hb : vBon F Z ∈ I := by
      by_contra hb; simp [hb] at heq; omega
    have hsum_eq : Finset.univ.sum cGain + lossFn F Z X = 2 * clauseW F Z := by
      simp [hb] at heq; omega
    have hidx_eq : ∀ idx : PosIdx F Z, cGain idx + cLoss idx = 2 * ((F Z)[idx.1.val]).2 := by
      intro idx
      by_contra hlt
      have hlt' : cGain idx + cLoss idx < 2 * ((F Z)[idx.1.val]).2 :=
        lt_of_le_of_ne (hclause idx).1 hlt
      have hstrict : Finset.univ.sum (fun j : PosIdx F Z => cGain j + cLoss j) <
          Finset.univ.sum (fun j : PosIdx F Z => 2 * ((F Z)[j.1.val]).2) :=
        Finset.sum_lt_sum (fun j _ => (hclause j).1) ⟨idx, Finset.mem_univ idx, hlt'⟩
      rw [Finset.sum_add_distrib, ← hloss_eq, ← Finset.mul_sum, ← hclauseW_eq] at hstrict
      change Finset.univ.sum cGain + lossFn F Z X < 2 * clauseW F Z at hstrict
      omega
    ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨huI, huL⟩
      refine ⟨?_, huL⟩
      rcases u with _ | _ | _ | _ | Z0 | ⟨Z0, idx, r⟩
      · exact absurd trivial huL
      · exact absurd trivial huL
      · exact absurd trivial huL
      · exact absurd trivial huL
      · by_cases hZ0 : Z0 = Z
        · subst hZ0; simp [idealI]
        · exact absurd huI (hbon_ne Z0 hZ0)
      · by_cases hZ0 : Z0 = Z
        · subst hZ0; exact ((hclause idx).2 (hidx_eq idx) r).mp huI
        · exact absurd huI (hhlp_ne Z0 idx r hZ0)
    · rintro ⟨huId, huL⟩
      refine ⟨?_, huL⟩
      rcases u with _ | _ | _ | _ | Z0 | ⟨Z0, idx, r⟩
      · exact absurd trivial huL
      · exact absurd trivial huL
      · exact absurd trivial huL
      · exact absurd trivial huL
      · simp only [idealI, Finset.mem_filter, Finset.mem_univ, true_and] at huId
        subst huId; exact hb
      · have hZ0 : Z0 = Z := by
          simp only [idealI, Finset.mem_filter, Finset.mem_univ, true_and] at huId
          exact huId.1
        subst hZ0
        exact ((hclause idx).2 (hidx_eq idx) r).mpr huId

open scoped Classical in
private lemma idealI_filter_heavy (Z : Finset (Fin d)) (X : Finset (Fin k)) :
    (idealI F Z X).filter (isHeavy F) = reqHeavy F Z X := by
  ext u
  rcases u with j | ⟨j, b⟩ | ⟨i, b⟩ | b | Z0 | ⟨Z0, idx, r⟩
  · simp [idealI, reqHeavy, isHeavy]
  · simp [idealI, reqHeavy, isHeavy]
  · cases b <;> simp [idealI, reqHeavy, isHeavy]
  · simp [idealI, reqHeavy, isHeavy]
  · simp [idealI, reqHeavy, isHeavy]
  · simp [idealI, reqHeavy, isHeavy]

open scoped Classical in
private lemma idealI_sum_eq (Z : Finset (Fin d)) (X : Finset (Fin k)) :
    (idealI F Z X).sum (wtV F) + lossFn F Z X = (2 * d + k + 2) * Hval F + Mval F := by
  have hsplit : (idealI F Z X).sum (wtV F) =
      ((idealI F Z X).filter (isHeavy F)).sum (wtV F) +
      ((idealI F Z X).filter (fun u => ¬ isHeavy F u)).sum (wtV F) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [hsplit, idealI_filter_heavy F Z X, reqHeavy_sum F Z X]
  have hbon_ne : ∀ Z0 : Finset (Fin d), Z0 ≠ Z → vBon F Z0 ∉ idealI F Z X := fun Z0 hne => by
    simp [idealI, vBon, hne]
  have hhlp_ne : ∀ Z0 (idx : PosIdx F Z0) (r : Fin 3), Z0 ≠ Z → vHlp F Z0 idx r ∉ idealI F Z X :=
    fun Z0 idx r hne => by simp [idealI, vHlp, hne]
  rw [light_sum_decomp F Z (idealI F Z X) hbon_ne hhlp_ne]
  have hbon_in : vBon F Z ∈ idealI F Z X := by simp [idealI, vBon]
  simp only [hbon_in, ↓reduceIte]
  have hclauseW_eq : clauseW F Z = Finset.univ.sum (fun idx : PosIdx F Z => ((F Z)[idx.1.val]).2) := by
    rw [clauseW, list_sum_fin_eq, ← sum_posIdx_eq F Z (fun i => ((F Z)[i.val]).2) (fun _ h => h)]
  have hloss_eq : lossFn F Z X = Finset.univ.sum (fun idx : PosIdx F Z =>
      if ((F Z)[idx.1.val]).1.1.elim True (fun a => a ∈ X) ∧ ((F Z)[idx.1.val]).1.2.elim True (fun b => b ∉ X)
      then ((F Z)[idx.1.val]).2 else 0) := by
    rw [lossFn, list_sum_fin_eq, ← sum_posIdx_eq F Z (fun i =>
      if ((F Z)[i.val]).1.1.elim True (fun a => a ∈ X) ∧ ((F Z)[i.val]).1.2.elim True (fun b => b ∉ X)
      then ((F Z)[i.val]).2 else 0) (fun i h => by simp [h])]
  have hsum_cl : Finset.univ.sum (fun idx : PosIdx F Z =>
      (if vHlp F Z idx 0 ∈ idealI F Z X then ((F Z)[idx.1.val]).2 else 0) +
      (if vHlp F Z idx 1 ∈ idealI F Z X then 2 * ((F Z)[idx.1.val]).2 else 0) +
      (if vHlp F Z idx 2 ∈ idealI F Z X then ((F Z)[idx.1.val]).2 else 0)) + lossFn F Z X =
      2 * clauseW F Z := by
    rw [hloss_eq, hclauseW_eq, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun idx _ => ?_
    by_cases hu : ((F Z)[idx.1.val]).1.1.elim True (fun i => i ∈ X) <;>
      by_cases hv : ((F Z)[idx.1.val]).1.2.elim True (fun j => j ∉ X) <;>
      simp [idealI, vHlp, hu, hv] <;> omega
  have hM_ge : 2 * clauseW F Z < Mval F := by
    have hle := Finset.le_sup (f := fun Z' : Finset (Fin d) => 2 * clauseW F Z') (Finset.mem_univ Z)
    dsimp only [Mval]; omega
  omega

open scoped Classical in
private lemma Gmax_le_totalW :
    (2 * d + k + 2) * Hval F + Mval F ≤ Finset.univ.sum (wtV F) := by
  let sub : Finset (V F) :=
    reqHeavy F ∅ ∅ ∪ ({vBon F ∅} ∪ Finset.univ.image (fun idx : PosIdx F ∅ => vHlp F ∅ idx 1))
  have hd1 : Disjoint (reqHeavy F ∅ ∅)
      ({vBon F ∅} ∪ Finset.univ.image (fun idx : PosIdx F ∅ => vHlp F ∅ idx 1)) := by
    refine Finset.disjoint_left.mpr fun u hu1 hu2 => ?_
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ, true_and] at hu2
    rcases hu2 with rfl | ⟨idx, rfl⟩
    · simp [reqHeavy, vBon] at hu1
    · simp [reqHeavy, vHlp] at hu1
  have hd2 : Disjoint ({vBon F ∅} : Finset (V F))
      (Finset.univ.image (fun idx : PosIdx F ∅ => vHlp F ∅ idx 1)) := by
    refine Finset.disjoint_left.mpr fun u hu1 hu2 => ?_
    rw [Finset.mem_singleton.mp hu1] at hu2
    rcases Finset.mem_image.mp hu2 with ⟨idx, _, h⟩
    simp [vBon, vHlp] at h
  have hsum : sub.sum (wtV F) = (2 * d + k + 2) * Hval F + Mval F := by
    dsimp only [sub]
    rw [Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton, reqHeavy_sum F ∅ ∅]
    rw [Finset.sum_image (fun a _ b _ hab => by
      simp only [vHlp, Sum.inr.injEq, Sigma.mk.injEq] at hab
      exact (Prod.mk.inj (eq_of_heq hab.2)).1)]
    have hcl : ∑ idx : PosIdx F ∅, wtV F (vHlp F ∅ idx 1) = 2 * clauseW F ∅ := by
      rw [clauseW, list_sum_fin_eq, ← sum_posIdx_eq F ∅ (fun i => ((F ∅)[i.val]).2) (fun _ h => h),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun idx _ => by simp [wtV, vHlp]
    rw [hcl]
    have hM_ge : 2 * clauseW F ∅ < Mval F := by
      have hle := Finset.le_sup (f := fun Z' : Finset (Fin d) => 2 * clauseW F Z') (Finset.mem_univ ∅)
      dsimp only [Mval]; omega
    simp only [wtV, vBon]
    omega
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ sub)

open scoped Classical in
private lemma main_proof (k d : Nat) (F : Finset (Fin d) → List ((Option (Fin k) × Option (Fin k)) × Nat)) :
    ∃ (N K : Nat) (G : Finset (Fin N × Fin N)) (w : Fin N → Nat)
      (s : Fin d → Fin N) (p : Fin k × Bool → Fin N) (S : Finset (Fin N)),
      (∀ e ∈ G, e.1 < e.2) ∧ (∀ v, 0 < w v) ∧
      Function.Injective s ∧ Function.Injective p ∧ Disjoint (Finset.univ.image s) (Finset.univ.image p) ∧
      (∀ e ∈ G, e.1 ∉ Finset.univ.image s → e.2 ∉ Finset.univ.image s → (e.1 ∈ S ↔ e.2 ∉ S)) ∧
      N ≤ 5*d+2*k+2+3*Finset.univ.sum (fun Z => (F Z).length)+2^d ∧
      ∀ Z X,
        let fits := fun (C : Finset (Fin N)) =>
          (∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧
          Finset.univ.filter (fun i => s i ∈ C) = Z ∧
          Finset.univ.filter (fun i => p (i, true) ∈ C) = X
        (∀ C, fits C → K + lossFn F Z X ≤ C.sum w) ∧
        (∃! C, fits C ∧ C.sum w = K + lossFn F Z X) ∧
        ∀ C, fits C → C.sum w = K + lossFn F Z X → ∀ i, (p (i, false) ∈ C ↔ p (i, true) ∉ C) := by
  let e : V F ≃ Fin (Fintype.card (V F)) := Fintype.equivFin (V F)
  let N := Fintype.card (V F)
  let w : Fin N → ℕ := fun x => wtV F (e.symm x)
  let G : Finset (Fin N × Fin N) :=
    Finset.univ.filter (fun pq => pq.1 < pq.2 ∧ adj F (e.symm pq.1) (e.symm pq.2))
  let s : Fin d → Fin N := fun j => e (vSel F j)
  let p : Fin k × Bool → Fin N := fun ib => e (vRaw F ib.1 ib.2)
  let S : Finset (Fin N) := Finset.univ.filter (fun x => isSide F (e.symm x) = true)
  let totalW : ℕ := Finset.univ.sum (wtV F)
  let Gmax : ℕ := (2 * d + k + 2) * Hval F + Mval F
  let K : ℕ := totalW - Gmax
  have hGmax_le : Gmax ≤ totalW := Gmax_le_totalW F
  have hcover_iff : ∀ C : Finset (Fin N),
      (∀ pq ∈ G, pq.1 ∈ C ∨ pq.2 ∈ C) ↔ isIndep F (Finset.univ.filter (fun u : V F => e u ∉ C)) := by
    intro C
    constructor
    · intro hC u v huv hu hv
      have hu' : e u ∉ C := (Finset.mem_filter.mp hu).2
      have hv' : e v ∉ C := (Finset.mem_filter.mp hv).2
      have hne : e u ≠ e v := fun h => adj_ne F huv (e.injective h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hmem : (e u, e v) ∈ G := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, ?_⟩
          simpa using huv
        rcases hC (e u, e v) hmem with h1 | h2
        · exact hu' h1
        · exact hv' h2
      · have hmem : (e v, e u) ∈ G := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt, ?_⟩
          simp only [e.symm_apply_apply]
          exact Or.symm huv
        rcases hC (e v, e u) hmem with h1 | h2
        · exact hv' h1
        · exact hu' h2
    · intro hI pq hpq
      rcases (Finset.mem_filter.mp hpq).2 with ⟨_, hadj⟩
      by_contra h
      have h' := not_or.mp h
      exact hI _ _ hadj (by simp [h'.1]) (by simp [h'.2])
  refine ⟨N, K, G, w, s, p, S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pq hpq; exact (Finset.mem_filter.mp hpq).2.1
  · intro x; exact wtV_pos F (e.symm x)
  · intro j1 j2 h; exact Sum.inl.inj (e.injective h)
  · intro a b h
    have h' := e.injective h
    simp only [vRaw, Sum.inr.injEq, Sum.inl.injEq] at h'
    exact h'
  · refine Finset.disjoint_left.mpr fun x h1 h2 => ?_
    rcases Finset.mem_image.mp h1 with ⟨j, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨ib, _, h⟩
    have h' := e.injective h
    simp [vSel, vRaw] at h'
  · intro pq hpq h1 h2
    have hadj := (Finset.mem_filter.mp hpq).2.2
    have hu : ¬ isSel F (e.symm pq.1) := by
      intro hsel
      rcases h1' : e.symm pq.1 with j | _ | _ | _ | _ | _
      · exact h1 (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, by simp [s, vSel, ← h1']⟩)
      all_goals rw [h1'] at hsel; exact hsel
    have hv : ¬ isSel F (e.symm pq.2) := by
      intro hsel
      rcases h2' : e.symm pq.2 with j | _ | _ | _ | _ | _
      · exact h2 (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, by simp [s, vSel, ← h2']⟩)
      all_goals rw [h2'] at hsel; exact hsel
    have hneq := adj_bip F hadj hu hv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    cases ha : isSide F (e.symm pq.1) <;> cases hb : isSide F (e.symm pq.2) <;> simp_all
  · exact card_V_le F
  · intro Z X fits
    have hsum_comp : ∀ C : Finset (Fin N),
        C.sum w + (Finset.univ.filter (fun u : V F => e u ∉ C)).sum (wtV F) = totalW := by
      intro C
      have hC_eq : C.sum w = (Finset.univ.filter (fun u : V F => e u ∈ C)).sum (wtV F) := by
        refine Finset.sum_bij (fun x _ => e.symm x) ?_ ?_ ?_ ?_
        · intro x hx; simp [hx]
        · intro x1 _ x2 _ h; exact e.symm.injective h
        · intro u hu; exact ⟨e u, (Finset.mem_filter.mp hu).2, e.symm_apply_apply u⟩
        · intro x _; rfl
      rw [hC_eq]
      exact Finset.sum_filter_add_sum_filter_not Finset.univ (fun u : V F => e u ∈ C) (wtV F)
    have hmain : ∀ C : Finset (Fin N), fits C →
        K + lossFn F Z X ≤ C.sum w ∧
        (C.sum w = K + lossFn F Z X →
          Finset.univ.filter (fun u : V F => e u ∉ C) = idealI F Z X) := by
      intro C ⟨hcov, hvs, hvp⟩
      let I := Finset.univ.filter (fun u : V F => e u ∉ C)
      have hI : isIndep F I := (hcover_iff C).mp hcov
      have hsel : ∀ j : Fin d, vSel F j ∈ I ↔ j ∉ Z := by
        intro j
        have hj : j ∈ Z ↔ s j ∈ C := by rw [← hvs]; simp
        simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
        exact not_iff_not.mpr hj.symm
      have hrawT : ∀ i : Fin k, vRaw F i true ∈ I ↔ i ∉ X := by
        intro i
        have hi : i ∈ X ↔ p (i, true) ∈ C := by rw [← hvp]; simp
        simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
        exact not_iff_not.mpr hi.symm
      have hH := heavy_props F Z X I hI hsel hrawT
      have hI_split : I.sum (wtV F) =
          (I.filter (isHeavy F)).sum (wtV F) + (I.filter (fun u => ¬ isHeavy F u)).sum (wtV F) := by
        rw [Finset.sum_filter_add_sum_filter_not]
      have hlight_all : (I.filter (fun u => ¬ isHeavy F u)).sum (wtV F) < Hval F := by
        have h1 : (I.filter (fun u => ¬ isHeavy F u)).sum (wtV F) =
            (I.filter (fun u => ¬ isHeavy F u)).sum (lightW F) :=
          Finset.sum_congr rfl fun u hu => wtV_light F u (Finset.mem_filter.mp hu).2
        rw [h1]
        have h2 : (I.filter (fun u => ¬ isHeavy F u)).sum (lightW F) ≤ Finset.univ.sum (lightW F) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        dsimp only [Hval]; omega
      have hsc : C.sum w + I.sum (wtV F) = totalW := hsum_comp C
      by_cases hall : ∀ v ∈ reqHeavy F Z X, v ∈ I
      · have hmir : ∀ j b, j ∈ Z → vMir F j b ∈ I := fun j b hj =>
          hall (vMir F j b) (by simp [reqHeavy, vMir, hj])
        have hrawF : ∀ i, i ∈ X → vRaw F i false ∈ I := fun i hi =>
          hall (vRaw F i false) (by simp [reqHeavy, vRaw, hi])
        have hanc : vAnc F false ∈ I ∧ vAnc F true ∈ I :=
          ⟨hall (vAnc F false) (by simp [reqHeavy, vAnc]), hall (vAnc F true) (by simp [reqHeavy, vAnc])⟩
        have hL := light_bound F Z X I hI hsel hmir hrawT hrawF hanc
        have hH_eq : I.filter (isHeavy F) = reqHeavy F Z X := by
          refine Finset.Subset.antisymm hH.1 fun u hu => ?_
          refine Finset.mem_filter.mpr ⟨hall u hu, ?_⟩
          rcases u with _ | _ | _ | _ | _ | _
          · trivial
          · trivial
          · trivial
          · trivial
          · simp [reqHeavy] at hu
          · simp [reqHeavy] at hu
        have hH_sum : (I.filter (isHeavy F)).sum (wtV F) = (2 * d + k + 2) * Hval F := by
          rw [hH_eq, reqHeavy_sum F Z X]
        constructor
        · dsimp only [K, Gmax] at *; omega
        · intro heq
          have hLeq : (I.filter (fun u => ¬ isHeavy F u)).sum (wtV F) + lossFn F Z X = Mval F := by
            dsimp only [K, Gmax] at *; omega
          have hL_eq := hL.2 hLeq
          ext u
          by_cases hHu : isHeavy F u
          · have h1 : u ∈ I ↔ u ∈ I.filter (isHeavy F) := by simp [hHu]
            have h2 : u ∈ idealI F Z X ↔ u ∈ (idealI F Z X).filter (isHeavy F) := by simp [hHu]
            rw [h1, h2, hH_eq, idealI_filter_heavy F Z X]
          · have h1 : u ∈ I ↔ u ∈ I.filter (fun v => ¬ isHeavy F v) := by simp [hHu]
            have h2 : u ∈ idealI F Z X ↔ u ∈ (idealI F Z X).filter (fun v => ¬ isHeavy F v) := by simp [hHu]
            rw [h1, h2, hL_eq]
      · rcases Classical.not_forall.mp hall with ⟨v, hv⟩
        rcases Classical.not_imp.mp hv with ⟨hv_req, hvI⟩
        have hH_lt := hH.2 v hv_req hvI
        have hloss_le_M : lossFn F Z X ≤ Mval F := by
          have h1 := idealI_sum_eq F Z X
          have h2 : (2 * d + k + 2) * Hval F ≤ (idealI F Z X).sum (wtV F) := by
            rw [← reqHeavy_sum F Z X, ← idealI_filter_heavy F Z X]
            exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
          omega
        have hstrict : I.sum (wtV F) + lossFn F Z X < Gmax := by
          dsimp only [Gmax]; omega
        constructor
        · dsimp only [K] at *; omega
        · intro heq; exfalso; dsimp only [K] at *; omega
    let Cstar : Finset (Fin N) := Finset.univ.filter (fun x => e.symm x ∉ idealI F Z X)
    have hCstar_I : Finset.univ.filter (fun u : V F => e u ∉ Cstar) = idealI F Z X := by
      ext u; simp [Cstar]
    have hCstar_fits : fits Cstar := by
      refine ⟨(hcover_iff Cstar).mpr (by rw [hCstar_I]; exact idealI_indep F Z X), ?_, ?_⟩
      · ext j; simp [Cstar, s, idealI, vSel]
      · ext i; simp [Cstar, p, idealI, vRaw]
    have hCstar_sum : Cstar.sum w = K + lossFn F Z X := by
      have hsc := hsum_comp Cstar
      rw [hCstar_I] at hsc
      have hid := idealI_sum_eq F Z X
      dsimp only [K, Gmax] at *
      omega
    refine ⟨fun C hC => (hmain C hC).1, ⟨Cstar, ⟨hCstar_fits, hCstar_sum⟩, ?_⟩, ?_⟩
    · intro C ⟨hCfits, hCsum⟩
      have hIeq := (hmain C hCfits).2 hCsum
      ext x
      have hx := Finset.ext_iff.mp hIeq (e.symm x)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, e.apply_symm_apply, Cstar] at hx ⊢
      by_cases h : x ∈ C <;> simp_all
    · intro C hCfits hCsum i
      have hIeq := (hmain C hCfits).2 hCsum
      have h0 := Finset.ext_iff.mp hIeq (vRaw F i false)
      have h1 := Finset.ext_iff.mp hIeq (vRaw F i true)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, idealI, vRaw] at h0 h1
      change e (vRaw F i false) ∈ C ↔ e (vRaw F i true) ∉ C
      simp only [vRaw]
      by_cases hi : i ∈ X <;> simp_all

end Construction

end PEqualNP.Outside.L_lib_1507

theorem PEqualNP.Outside.L_lib_1507 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let cover := fun {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
let opt := fun {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (C : Finset (Fin N)) =>
  cover G C ∧ ∀ B, cover G B → C.sum w ≤ B.sum w
let bip := fun {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
let view := fun {k N : Nat} (p : Fin k → Fin N) (C : Finset (Fin N)) =>
  Finset.univ.filter (fun i => p i ∈ C)
∀ (k d : Nat) (F : Finset (Fin d) → List ((Option (Fin k) × Option (Fin k)) × Nat)),
let loss := fun (Z : Finset (Fin d)) (X : Finset (Fin k)) =>
  ((F Z).map (fun c =>
    if c.1.1.elim True (fun i => i ∈ X) ∧ c.1.2.elim True (fun j => j ∉ X)
    then c.2 else 0)).sum
∃ (N K : Nat) (G : Finset (Fin N × Fin N)) (w : Fin N → Nat)
  (s : Fin d → Fin N) (p : Fin k × Bool → Fin N) (S : Finset (Fin N)),
  (∀ e ∈ G, e.1<e.2) ∧ (∀ v, 0<w v) ∧
  Function.Injective s ∧ Function.Injective p ∧ Disjoint (Finset.univ.image s) (Finset.univ.image p) ∧
  bip G (Finset.univ.image s) S ∧
  N ≤ 5*d+2*k+2+3*Finset.univ.sum (fun Z => (F Z).length)+2^d ∧
  ∀ Z X,
    let fits := fun (C : Finset (Fin N)) => cover G C ∧ view s C=Z ∧ view (fun i => p (i,true)) C=X
    (∀ C, fits C → K+loss Z X ≤ C.sum w) ∧ (∃! C, fits C ∧ C.sum w=K+loss Z X) ∧
    ∀ C, fits C → C.sum w=K+loss Z X → ∀ i, (p (i,false) ∈ C ↔ p (i,true) ∉ C)) := by
  intro cover opt bip view k d F loss
  rcases PEqualNP.Outside.L_lib_1507.main_proof k d F with
    ⟨N, K, G, w, s, p, S, h1, h2, h3, h4, h5, h6, h7, h8⟩
  refine ⟨N, K, G, w, s, p, S, h1, h2, h3, h4, ?_, ?_, h7, fun Z X => ?_⟩
  · refine Finset.disjoint_left.mpr fun x hx1 hx2 =>
      Finset.disjoint_left.mp h5 (by simpa using hx1) (by simpa using hx2)
  · intro e he h1' h2'
    exact h6 e he (by simpa using h1') (by simpa using h2')
  have hloss : loss Z X = PEqualNP.Outside.L_lib_1507.lossFn F Z X := by
    dsimp only [loss, PEqualNP.Outside.L_lib_1507.lossFn]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    by_cases h : c.1.1.elim True (fun i => i ∈ X) ∧ c.1.2.elim True (fun j => j ∉ X) <;>
      simp [h]
  have hfits : ∀ C : Finset (Fin N),
      (cover G C ∧ view s C = Z ∧ view (fun i => p (i, true)) C = X) ↔
      ((∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧
       Finset.univ.filter (fun i => s i ∈ C) = Z ∧
       Finset.univ.filter (fun i => p (i, true) ∈ C) = X) := by
    intro C
    have hs : view s C = Finset.univ.filter (fun i => s i ∈ C) := by ext i; simp [view]
    have hp : view (fun i => p (i, true)) C = Finset.univ.filter (fun i => p (i, true) ∈ C) := by
      ext i; simp [view]
    rw [hs, hp]
  rcases h8 Z X with ⟨ha, ⟨Cstar, ⟨hCf, hCs⟩, hCu⟩, hc⟩
  refine ⟨fun C hC => by rw [hloss]; exact ha C ((hfits C).mp hC),
    ⟨Cstar, ⟨(hfits Cstar).mpr hCf, by rw [hloss]; exact hCs⟩,
      fun C ⟨hC1, hC2⟩ => hCu C ⟨(hfits C).mp hC1, by rw [← hloss]; exact hC2⟩⟩,
    fun C hC hsum => hc C ((hfits C).mp hC) (by rw [← hloss]; exact hsum)⟩
