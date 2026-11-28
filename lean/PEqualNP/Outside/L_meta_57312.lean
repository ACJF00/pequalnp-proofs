import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_29768

namespace PEqualNP.Outside.L_meta_57312

open MvPolynomial

private abbrev F := ZMod 2

private abbrev Poly (n : ℕ) := MvPolynomial (Fin n) F

private noncomputable def base {n : ℕ} (p : Poly (n+1)) : Poly n :=
  (finSuccEquiv F n p).coeff 0

private noncomputable def difference {n : ℕ} (p : Poly (n+1)) : Poly n :=
  ∑ j ∈ Finset.range (finSuccEquiv F n p).natDegree, (finSuccEquiv F n p).coeff (j+1)

private theorem base_degree {n d : ℕ} (p : Poly (n+1)) (hp : p.totalDegree ≤ d) :
    (base p).totalDegree ≤ d := by
  by_cases h : base p = 0
  · simp [h]
  · have := totalDegree_coeff_finSuccEquiv_add_le p 0 h
    exact (by simpa only [base, Nat.add_zero] using this : (base p).totalDegree ≤ _).trans hp

private theorem diff_degree {n d : ℕ} (p : Poly (n+1)) (hp : p.totalDegree ≤ d+1) :
    (difference p).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro j _
  by_cases h : (finSuccEquiv F n p).coeff (j+1) = 0
  · simp [h]
  · have := totalDegree_coeff_finSuccEquiv_add_le p (j+1) h
    omega

private theorem eval_base {n : ℕ} (p : Poly (n+1)) (x : Fin n → F) :
    eval (Fin.cons 0 x) p = eval x (base p) := by
  rw [eval_eq_eval_mv_eval', ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
  rfl

private theorem eval_one_slice {n : ℕ} (p : Poly (n+1)) (x : Fin n → F) :
    eval (Fin.cons 1 x) p = eval x (base p) + eval x (difference p) := by
  rw [eval_eq_eval_mv_eval', Polynomial.eval_one_map, ← map_add]
  congr 1
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
  simp only [one_pow, mul_one, base, difference, add_comm]

private noncomputable def supportAt {n : ℕ} (p : Poly n) : Finset (Fin n → F) := by
  classical
  exact Finset.univ.filter (fun x => eval x p ≠ 0)

private theorem mem_supportAt {n : ℕ} (p : Poly n) (x : Fin n → F) :
    x ∈ supportAt p ↔ eval x p ≠ 0 := by
  classical
  simp [supportAt]

private theorem split_count (n : ℕ) (P : (Fin (n+1) → F) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun x : Fin n → F => P (Fin.cons 0 x))).card +
      (Finset.univ.filter (fun x : Fin n → F => P (Fin.cons 1 x))).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  let f := fun z : Fin (n+1) → F => if P z then (1 : ℕ) else 0
  change (∑ z, f z) = (∑ x : Fin n → F, f (Fin.cons 0 x)) + (∑ x : Fin n → F, f (Fin.cons 1 x))
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => F)).sum_comp f, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply]
  rw [show (Finset.univ : Finset F) = {0,1} by decide +kernel]
  simp

private theorem constant_count {n : ℕ} (p : Poly n) (hp : p.totalDegree = 0)
    (hne : ∃ x : Fin n → F, eval x p ≠ 0) : (supportAt p).card = 2^n := by
  classical
  have heq := totalDegree_eq_zero_iff_eq_C.mp hp
  obtain ⟨x,hx⟩ := hne
  have hc : p.coeff 0 ≠ 0 := by
    rwa [heq, eval_C] at hx
  have hs : supportAt p = Finset.univ := by
    ext x
    simp only [mem_supportAt, Finset.mem_univ, iff_true]
    rw [heq, eval_C]
    exact hc
  rw [hs]
  simp

private theorem estimate (n : ℕ) : ∀ (d : ℕ) (p : Poly n), p.totalDegree ≤ d →
    (∃ x : Fin n → F, eval x p ≠ 0) → 2^n ≤ 2^d * (supportAt p).card := by
  classical
  induction n with
  | zero =>
    intro d p _ hp
    obtain ⟨x,hx⟩ := hp
    have pos := Finset.card_pos.mpr ⟨x, (mem_supportAt p x).mpr hx⟩
    exact Nat.mul_pos (by positivity) pos
  | succ n ih =>
    intro d p hp hne
    cases d with
    | zero => rw [constant_count p (Nat.eq_zero_of_le_zero hp) hne, pow_zero, one_mul]
    | succ d =>
      let q := base p
      let r := difference p
      let count0 := Finset.univ.filter (fun x : Fin n → F => eval (Fin.cons 0 x) p ≠ 0)
      let count1 := Finset.univ.filter (fun x : Fin n → F => eval (Fin.cons 1 x) p ≠ 0)
      have hf : (supportAt p).card = count0.card + count1.card := split_count n _
      have h0 : count0 = supportAt q := by
        ext x
        simp [count0, mem_supportAt, q, eval_base]
      by_cases hr : ∃ x : Fin n → F, eval x r ≠ 0
      · have hb := ih d r (diff_degree p hp) hr
        have diff_support : supportAt r ⊆ count0 ∪ count1 := by
          intro x hx
          have hxr := (mem_supportAt r x).mp hx
          by_contra miss
          have hleft : eval (Fin.cons 0 x) p = 0 := by
            by_contra notZero
            exact miss (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,notZero⟩))
          have hright : eval (Fin.cons 1 x) p = 0 := by
            by_contra notZero
            exact miss (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,notZero⟩))
          rw [eval_base] at hleft
          rw [eval_one_slice, hleft, zero_add] at hright
          exact hxr hright
        have hc : (supportAt r).card ≤ (supportAt p).card := by
          rw [hf]
          exact (Finset.card_le_card diff_support).trans (Finset.card_union_le _ _)
        calc
          2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
          _ ≤ 2 * (2 ^ d * (supportAt p).card) :=
            Nat.mul_le_mul_left 2 (hb.trans (Nat.mul_le_mul_left _ hc))
          _ = 2 ^ (d + 1) * (supportAt p).card := by rw [pow_succ]; ring
      · have zero_r (x : Fin n → F) : eval x r = 0 := not_ne_iff.mp (not_exists.mp hr x)
        have h1 : count1 = supportAt q := by
          ext x
          simp only [count1, Finset.mem_filter_univ, mem_supportAt, eval_one_slice]
          change eval x q + eval x r ≠ 0 ↔ eval x q ≠ 0
          rw [zero_r, add_zero]
        obtain ⟨x,hx⟩ := hne
        let z := Fin.tail x
        have hhead : x 0 = 0 ∨ x 0 = 1 := by
          have hz : ∀ b : F, b = 0 ∨ b = 1 := by decide +kernel
          exact hz (x 0)
        have hqn : eval z q ≠ 0 := by
          have he : Fin.cons (x 0) z = x := Fin.cons_self_tail x
          rw [← he] at hx
          rcases hhead with hh | hh
          · simpa only [hh, eval_base] using hx
          · simpa only [hh, eval_one_slice, show eval z (difference p) = 0 from zero_r z, add_zero] using hx
        have hb := ih (d+1) q (base_degree p hp) ⟨z,hqn⟩
        rw [hf, h0, h1, pow_succ, Nat.mul_add]
        omega

private theorem det_one_add {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod 2)) :
    (1 + M).det = ∑ J : Finset ι,
      (M.submatrix (fun i : ↥J => i.val) (fun j : ↥J => j.val)).det := by
  have h := (Matrix.detRowAlternating (R := ZMod 2) (n := ι)).toMultilinearMap.map_add_univ M (1 : Matrix ι ι (ZMod 2))
  rw [add_comm]
  have h' : (M + 1).det = ∑ J : Finset ι, (Matrix.of (J.piecewise M (1 : Matrix ι ι (ZMod 2)))).det := h
  refine h'.trans (Finset.sum_congr rfl fun J _ => ?_)
  rw [Matrix.twoBlockTriangular_det _ (fun i => i ∈ J)]
  · have h1 : Matrix.toSquareBlockProp (Matrix.of (J.piecewise M (1 : Matrix ι ι (ZMod 2)))) (fun i => i ∈ J) =
        M.submatrix (fun i : ↥J => i.val) (fun j : ↥J => j.val) := by
      ext i j
      simp [Matrix.toSquareBlockProp, Matrix.toBlock, Finset.piecewise, i.2]
    have h2 : Matrix.toSquareBlockProp (Matrix.of (J.piecewise M (1 : Matrix ι ι (ZMod 2)))) (fun i => ¬ i ∈ J) = 1 := by
      ext i j
      simp [Matrix.toSquareBlockProp, Matrix.toBlock, Finset.piecewise, i.2, Matrix.one_apply,
        Subtype.ext_iff]
    rw [h1, h2, Matrix.det_one, mul_one]
    convert rfl
  · intro i hi j hj
    have hne : i ≠ j := fun e => hi (e ▸ hj)
    simp [Finset.piecewise, hi, hne]

private def restr {ι : Type} [DecidableEq ι] (H : Matrix ι ι (ZMod 2)) (R : Finset ι) :
    Matrix ι ι (ZMod 2) :=
  fun i j => if j ∈ R then H i j else 0

private theorem det_sub_restr {ι : Type} [DecidableEq ι] (H : Matrix ι ι (ZMod 2))
    (R J : Finset ι) :
    ((restr H R).submatrix (fun i : ↥J => i.val) (fun j : ↥J => j.val)).det =
      if J ⊆ R then (H.submatrix (fun i : ↥J => i.val) (fun j : ↥J => j.val)).det else 0 := by
  split_ifs with h
  · congr 1
    ext i j
    simp [restr, h j.2]
  · obtain ⟨j, hjJ, hjR⟩ := Finset.not_subset.mp h
    exact Matrix.det_eq_zero_of_column_eq_zero ⟨j, hjJ⟩ (fun i => by simp [restr, hjR])

private def minorSum {s : ℕ} (H : Matrix (Fin s × Fin 2) (Fin s × Fin 2) (ZMod 2))
    (U : Finset (Fin s)) : ZMod 2 :=
  ∑ J ∈ ((Finset.univ : Finset (Fin s × Fin 2)).powerset.filter
    (fun J => J.image Prod.fst = U)),
    Matrix.det (Matrix.submatrix H (fun i : ↥J => i.val) (fun j : ↥J => j.val))

private theorem minorSum_empty {s : ℕ} (H : Matrix (Fin s × Fin 2) (Fin s × Fin 2) (ZMod 2)) :
    minorSum H ∅ = 1 := by
  have hf : ((Finset.univ : Finset (Fin s × Fin 2)).powerset.filter
      (fun J => J.image Prod.fst = ∅)) = {∅} := by
    ext J
    simp [Finset.image_eq_empty]
  rw [minorSum, hf, Finset.sum_singleton]
  exact Matrix.det_isEmpty

private theorem compress {s : ℕ} (H : Matrix (Fin s × Fin 2) (Fin s × Fin 2) (ZMod 2))
    (U : Finset (Fin s)) :
    (1 + restr H (U ×ˢ (Finset.univ : Finset (Fin 2)))).det =
      ∑ U' ∈ U.powerset, minorSum H U' := by
  rw [det_one_add]
  simp only [det_sub_restr]
  rw [← Finset.sum_filter]
  have hmaps : ∀ J ∈ (Finset.univ : Finset (Finset (Fin s × Fin 2))).filter
      (fun J => J ⊆ U ×ˢ (Finset.univ : Finset (Fin 2))),
      J.image Prod.fst ∈ U.powerset := by
    intro J hJ
    rw [Finset.mem_powerset]
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp ((Finset.mem_filter.mp hJ).2 hx)).1
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun U' hU' => ?_
  rw [minorSum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext J
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset,
    Finset.subset_univ]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    intro x hx
    rw [Finset.mem_product]
    refine ⟨Finset.mem_powerset.mp hU' ?_, Finset.mem_univ _⟩
    rw [← h]
    exact Finset.mem_image_of_mem _ hx

private theorem zmod2_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t
  decide

private theorem invert {s : ℕ} (mf : Finset (Fin s) → ZMod 2) (h0 : mf ∅ = 1)
    (h : ∀ U : Finset (Fin s), ∑ U' ∈ U.powerset, mf U' = 1) :
    ∀ U : Finset (Fin s), U.Nonempty → mf U = 0 := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
    intro hne
    have hU := h U
    have hUe : (∅ : Finset (Fin s)) ≠ U := fun e => Finset.not_nonempty_empty (e ▸ hne)
    rw [Finset.sum_eq_add_of_mem ∅ U (Finset.empty_mem_powerset U)
      (Finset.mem_powerset.mpr (Finset.Subset.refl U)) hUe] at hU
    · rw [h0] at hU
      rcases zmod2_cases (mf U) with e | e
      · exact e
      · rw [e] at hU
        exact absurd hU (by decide)
    · intro c hcU hcne
      exact ih c (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hcU, hcne.2⟩)
        (Finset.nonempty_iff_ne_empty.mpr hcne.1)

private theorem block_det {s : ℕ} (H : Matrix (Fin s × Fin 2) (Fin s × Fin 2) (ZMod 2))
    (hlow : ∀ i j : Fin s × Fin 2, j.1 < i.1 → H i j = 0)
    (hdiag : ∀ a : Fin s,
      (1 + H (a,0) (a,0)) * (1 + H (a,1) (a,1)) + H (a,0) (a,1) * H (a,1) (a,0) = 1)
    (U : Finset (Fin s)) :
    (1 + restr H (U ×ˢ (Finset.univ : Finset (Fin 2)))).det = 1 := by
  have hbt : Matrix.BlockTriangular (1 + restr H (U ×ˢ (Finset.univ : Finset (Fin 2)))) Prod.fst := by
    intro i j hij
    have hne : i ≠ j := fun e => by
      rw [e] at hij
      exact lt_irrefl _ hij
    simp [restr, Matrix.one_apply, hne, hlow i j hij]
  rw [hbt.det_fintype]
  apply Finset.prod_eq_one
  intro a _
  let e : Fin 2 ≃ {i : Fin s × Fin 2 // i.1 = a} :=
    { toFun := fun p => ⟨(a, p), rfl⟩
      invFun := fun i => i.1.2
      left_inv := fun p => rfl
      right_inv := fun i => by
        rcases i with ⟨⟨b, p⟩, rfl⟩
        rfl }
  rw [← Matrix.det_submatrix_equiv_self e, Matrix.det_fin_two]
  have hd := hdiag a
  have h2 : ∀ x y : ZMod 2, x - y = x + y := by decide
  rw [h2]
  by_cases ha : a ∈ U
  · simpa [Matrix.toSquareBlock, Matrix.toSquareBlockProp, Matrix.toBlock, e, restr,
      Matrix.one_apply, ha] using hd
  · simp [Matrix.toSquareBlock, Matrix.toSquareBlockProp, Matrix.toBlock, e, restr,
      Matrix.one_apply, ha]

private theorem lin_poly {d : ℕ} (l : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    ∃ p : MvPolynomial (Fin d) (ZMod 2), p.totalDegree ≤ 1 ∧ ∀ x, eval x p = l x := by
  refine ⟨∑ t, C (l (fun t' => if t = t' then 1 else 0)) * X t, ?_, ?_⟩
  · apply totalDegree_finsetSum_le
    intro t _
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X])
  · intro x
    rw [LinearMap.pi_apply_eq_sum_univ l x]
    simp [mul_comm]

private theorem deg_one_add {d : ℕ} (p : MvPolynomial (Fin d) (ZMod 2)) (h : p.totalDegree ≤ 1) :
    (1 + p).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans ?_
  simp [h]

private theorem sum_aux (s : ℕ) : ∑ i ∈ Finset.range s, (4 * i + 2) = 2 * s ^ 2 := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private theorem core {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    {s : ℕ} (W : Submodule (ZMod 2) K) (Z : Finset K) (hZW : ∀ z ∈ Z, z⁻¹ ∈ W)
    (u : Fin s × Fin 2 → K) (f : Fin s × Fin 2 → (K →ₗ[ZMod 2] ZMod 2))
    (hcrit : ∀ z ∈ Z, ∃ U : Finset (Fin s), U.Nonempty ∧
      minorSum (fun i j => f i (z⁻¹ * u j)) U ≠ 0) :
    Z.card + 2 ^ (Module.finrank (ZMod 2) W - 2 * s ^ 2) ≤ 2 ^ (Module.finrank (ZMod 2) W) := by
  classical
  generalize hd : Module.finrank (ZMod 2) W = d
  let bW : Module.Basis (Fin d) (ZMod 2) W := (Module.finBasis (ZMod 2) W).reindex (finCongr hd)
  let φ : (Fin d → ZMod 2) →ₗ[ZMod 2] K := W.subtype ∘ₗ bW.equivFun.symm.toLinearMap
  let L : Fin s × Fin 2 → Fin s × Fin 2 → ((Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2) :=
    fun i j => (f i) ∘ₗ (LinearMap.mulRight (ZMod 2) (u j)) ∘ₗ φ
  have hL : ∀ i j x, L i j x = f i (φ x * u j) := fun i j x => rfl
  choose lp hdeg hev using fun i j => lin_poly (L i j)
  let P : MvPolynomial (Fin d) (ZMod 2) :=
    ∏ a : Fin s, ((∏ b ∈ Finset.Iio a, ∏ p : Fin 2, ∏ q : Fin 2, (1 + lp (a,p) (b,q))) *
      ((1 + lp (a,0) (a,0)) * (1 + lp (a,1) (a,1)) + lp (a,0) (a,1) * lp (a,1) (a,0)))
  have hPev : ∀ x, eval x P =
      ∏ a : Fin s, ((∏ b ∈ Finset.Iio a, ∏ p : Fin 2, ∏ q : Fin 2, (1 + L (a,p) (b,q) x)) *
      ((1 + L (a,0) (a,0) x) * (1 + L (a,1) (a,1) x) + L (a,0) (a,1) x * L (a,1) (a,0) x)) := by
    intro x
    simp only [P, map_prod, map_mul, map_add, map_one, hev]
  have hPdeg : P.totalDegree ≤ 2 * s ^ 2 := by
    refine (totalDegree_finsetProd _ _).trans ?_
    rw [← sum_aux s, ← Fin.sum_univ_eq_sum_range (fun i => 4 * i + 2) s]
    apply Finset.sum_le_sum
    intro a _
    refine (totalDegree_mul _ _).trans (Nat.add_le_add ?_ ?_)
    · refine (totalDegree_finsetProd _ _).trans ?_
      have hc : (Finset.Iio a).card = (a : ℕ) := Fin.card_Iio a
      rw [← hc, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_le_sum
      intro b _
      refine (totalDegree_finsetProd _ _).trans ?_
      have h2 : ∀ p : Fin 2, (∏ q : Fin 2, (1 + lp (a,p) (b,q))).totalDegree ≤ 2 := by
        intro p
        refine (totalDegree_finsetProd _ _).trans ?_
        have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2)))
          (fun q _ => deg_one_add _ (hdeg (a,p) (b,q)))
        simpa using this
      have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2))) (fun p _ => h2 p)
      simpa using this
    · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_mul _ _).trans
          (Nat.add_le_add (deg_one_add _ (hdeg _ _)) (deg_one_add _ (hdeg _ _)))
      · exact (totalDegree_mul _ _).trans (Nat.add_le_add (hdeg _ _) (hdeg _ _))
  have hP0 : eval 0 P ≠ 0 := by
    rw [hPev]
    simp
  have hsupp := estimate d (2 * s ^ 2) P hPdeg ⟨0, hP0⟩
  have hgood : ∀ x, eval x P ≠ 0 → ∀ U : Finset (Fin s), U.Nonempty →
      minorSum (fun i j => f i (φ x * u j)) U = 0 := by
    intro x hx U hU
    rw [hPev, Finset.prod_ne_zero_iff] at hx
    have hlow : ∀ i j : Fin s × Fin 2, j.1 < i.1 → f i (φ x * u j) = 0 := by
      rintro ⟨a, p⟩ ⟨b, q⟩ hba
      have h1 := (mul_ne_zero_iff.mp (hx a (Finset.mem_univ _))).1
      rw [Finset.prod_ne_zero_iff] at h1
      have h2 := h1 b (Finset.mem_Iio.mpr hba)
      rw [Finset.prod_ne_zero_iff] at h2
      have h3 := h2 p (Finset.mem_univ _)
      rw [Finset.prod_ne_zero_iff] at h3
      have h4 := h3 q (Finset.mem_univ _)
      rcases zmod2_cases (L (a,p) (b,q) x) with e | e
      · exact e
      · rw [e] at h4
        exact absurd (by decide) h4
    have hdiag : ∀ a : Fin s, (1 + f (a,0) (φ x * u (a,0))) * (1 + f (a,1) (φ x * u (a,1))) +
        f (a,0) (φ x * u (a,1)) * f (a,1) (φ x * u (a,0)) = 1 := by
      intro a
      have h1 := (mul_ne_zero_iff.mp (hx a (Finset.mem_univ _))).2
      rcases zmod2_cases ((1 + L (a,0) (a,0) x) * (1 + L (a,1) (a,1) x) +
        L (a,0) (a,1) x * L (a,1) (a,0) x) with e | e
      · exact absurd e h1
      · exact e
    refine invert _ (minorSum_empty _) ?_ U hU
    intro U'
    have hc := compress (fun i j => f i (φ x * u j)) U'
    rw [block_det _ hlow hdiag U'] at hc
    exact hc.symm
  let g : K → (Fin d → ZMod 2) := fun z => if h : z⁻¹ ∈ W then bW.equivFun ⟨z⁻¹, h⟩ else 0
  have hφg : ∀ z ∈ Z, φ (g z) = z⁻¹ := by
    intro z hz
    simp [g, hZW z hz, φ]
  have hinj : Set.InjOn g Z := by
    intro a ha b hb hab
    have := congrArg φ hab
    rw [hφg a ha, hφg b hb] at this
    exact inv_injective this
  have hdisj : Disjoint (Z.image g) (supportAt P) := by
    rw [Finset.disjoint_left]
    intro x hx hxs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨U, hU, hne⟩ := hcrit z hz
    apply hne
    have := hgood (g z) ((mem_supportAt _ _).mp hxs) U hU
    rwa [hφg z hz] at this
  have hcard : (Z.image g).card + (supportAt P).card ≤ 2 ^ d := by
    rw [← Finset.card_union_of_disjoint hdisj]
    refine (Finset.card_le_univ _).trans (le_of_eq ?_)
    simp [ZMod.card]
  rw [Finset.card_image_of_injOn hinj] at hcard
  have hfin : 2 ^ (d - 2 * s ^ 2) ≤ (supportAt P).card := by
    by_cases hle : 2 * s ^ 2 ≤ d
    · have h2 : 2 ^ d = 2 ^ (2 * s ^ 2) * 2 ^ (d - 2 * s ^ 2) := by
        rw [← pow_add]
        congr 1
        omega
      rw [h2] at hsupp
      exact Nat.le_of_mul_le_mul_left hsupp (by positivity)
    · have h2 : d - 2 * s ^ 2 = 0 := by omega
      rw [h2, pow_zero]
      exact Finset.card_pos.mpr ⟨0, (mem_supportAt _ _).mpr hP0⟩
  omega

end PEqualNP.Outside.L_meta_57312

theorem PEqualNP.Outside.L_meta_57312 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (k : ℕ) (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
  let n := k+1
  let point : Fin n → K := Fin.cases 0 basis
  let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
  let residual := fun {g : ℕ} (T : Fin g → Fin n → Fin n → Bool) (S : Finset (Fin g))
      (z : K) (x y : Fin n) => xor (mult z x y) (((S.filter (fun i => T i x y)).card % 2) == 1)
  let serves := fun (s : ℕ) (Z : Finset K) =>
    ∃ (p : ℕ) (T : Fin p → Fin n → Fin n → Bool),
      fits n n p T s ∧ ∀ z ∈ Z, ∃ S : Finset (Fin p),
        fits n n 1 (fun _ => residual T S z) (k/2)

  k % 2 = 1 → ∀ (s : ℕ) (W : Submodule F K) (Z : Finset K),
    (0 : K) ∉ Z → (∀ z ∈ Z, z⁻¹ ∈ W) → serves s Z →
    let d := Module.finrank F W
    Z.card + 2^(d - 2*s^2) ≤ 2^d
) := by
  intro nonlinear depths fits F K _ _ _ k basis bit hbit n point mult residual serves odd s W Z hZ hZW hserve d
  obtain ⟨u, f, hcrit⟩ := (PEqualNP.Outside.L_meta_29768 K k basis bit hbit odd s Z hZ).mp hserve
  exact PEqualNP.Outside.L_meta_57312.core W Z hZW u f hcrit
