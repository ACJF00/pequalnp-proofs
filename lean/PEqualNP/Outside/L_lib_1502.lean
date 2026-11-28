import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1502_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def ValidPos (n : Nat) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.and, []⟩).inputs, i < n + j)

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepWire_length (w : List Bool) (gs : List Gate) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g t ih =>
    simp only [List.foldl_cons, ih, stepWire, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (d : α) {i : Nat} (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD, List.getElem?_append_left hi]

lemma foldl_stepWire_prefix (w : List Bool) (gs : List Gate) {i : Nat} (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g t ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hi']
    exact getD_append_left w _ false hi

lemma foldl_stepWire_append (w : List Bool) (gs1 gs2 : List Gate) :
    (gs1 ++ gs2).foldl stepWire w = gs2.foldl stepWire (gs1.foldl stepWire w) :=
  List.foldl_append

lemma getD_singleton_last {α : Type*} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp [List.getD]

lemma validPos_append {n : Nat} {gs1 gs2 : List Gate}
    (h1 : ValidPos n gs1) (h2 : ValidPos (n + gs1.length) gs2) :
    ValidPos n (gs1 ++ gs2) := by
  constructor
  · intro g hg
    rcases List.mem_append.mp hg with hg1 | hg2
    · exact h1.1 g hg1
    · exact h2.1 g hg2
  · intro j hj i hi
    simp only [List.length_append] at hj
    by_cases hlt : j < gs1.length
    · rw [getD_append_left gs1 gs2 _ hlt] at hi
      exact h1.2 j hlt i hi
    · have hj2 : j - gs1.length < gs2.length := by omega
      have hget : (gs1 ++ gs2).getD j ⟨GateOp.and, []⟩ = gs2.getD (j - gs1.length) ⟨GateOp.and, []⟩ := by
        simp only [List.getD, List.getElem?_append_right (Nat.le_of_not_lt hlt)]
      rw [hget] at hi
      have := h2.2 (j - gs1.length) hj2 i hi
      omega

lemma validPos_to_pos {n : Nat} (C : Circuit) (hv : ValidPos (n + 2) C.gates) (ho : C.output < n + 2 + C.size) :
    FanInTwo C ∧ ReadsBack (n + 2) C ∧ C.output < n + 2 + C.size ∧ PEqualNP.NotBracket.notCount C = 0 := by
  refine ⟨?_, ?_, ho, ?_⟩
  · intro g hg
    have h1 := hv.1 g hg
    refine ⟨?_, h1.2⟩
    rcases h1.1 with h2 | h2 <;> simp [h2]
  · intro j hj i hi
    have hgate : gateAt C j = C.gates.getD j ⟨GateOp.and, []⟩ := by
      simp only [gateAt, List.getD, List.getElem?_eq_getElem hj, Option.getD_some]
    rw [hgate] at hi
    exact hv.2 j hj i hi
  · unfold PEqualNP.NotBracket.notCount
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro g hg
    have h1 := (hv.1 g hg).1
    rcases h1 with h2 | h2 <;> simp [h2]

def chainAux (op : GateOp) : Nat → Nat → List Nat → List Gate × Nat
  | _, cur, [] => ([], cur)
  | base, cur, a :: rest =>
    let r := chainAux op (base + 1) base rest
    (⟨op, [cur, a]⟩ :: r.1, r.2)

lemma chainAux_length (op : GateOp) (base cur : Nat) (ws : List Nat) :
    (chainAux op base cur ws).1.length = ws.length := by
  induction ws generalizing base cur with
  | nil => rfl
  | cons a rest ih => simp [chainAux, ih]

lemma chainAux_out_lt (op : GateOp) (base cur : Nat) (ws : List Nat) (hcur : cur < base) :
    (chainAux op base cur ws).2 < base + ws.length := by
  induction ws generalizing base cur with
  | nil => simpa [chainAux] using hcur
  | cons a rest ih =>
    simp only [chainAux, List.length_cons]
    have := ih (base + 1) base (Nat.lt_succ_self base)
    omega

lemma chainAux_valid (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (base cur : Nat) (ws : List Nat) (hcur : cur < base) (hws : ∀ u ∈ ws, u < base) :
    ValidPos base (chainAux op base cur ws).1 := by
  induction ws generalizing base cur with
  | nil => exact ⟨by simp [chainAux], by simp [chainAux]⟩
  | cons a rest ih =>
    have hrest : ∀ u ∈ rest, u < base + 1 := fun u hu => Nat.lt_succ_of_lt (hws u (by simp [hu]))
    have hsub := ih (base + 1) base (Nat.lt_succ_self base) hrest
    constructor
    · intro g hg
      simp only [chainAux, List.mem_cons] at hg
      rcases hg with rfl | hgt
      · exact ⟨hop, by simp⟩
      · exact hsub.1 g hgt
    · intro j hj i hi
      simp only [chainAux, List.length_cons] at hj
      cases j with
      | zero =>
        simp only [chainAux, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · omega
        · have := hws i (by simp); omega
      | succ j' =>
        simp only [chainAux, List.getD_cons_succ] at hi
        have := hsub.2 j' (by omega) i hi
        omega

lemma chainAux_eval_or (base cur : Nat) (ws : List Nat) (w : List Bool)
    (hlen : w.length = base) (hcur : cur < base) (hws : ∀ u ∈ ws, u < base) :
    ((chainAux GateOp.or base cur ws).1.foldl stepWire w).getD (chainAux GateOp.or base cur ws).2 false =
    (w.getD cur false || ws.any (fun u => w.getD u false)) := by
  induction ws generalizing base cur w with
  | nil => simp [chainAux]
  | cons a rest ih =>
    simp only [chainAux, List.foldl_cons, List.any_cons]
    let w1 := stepWire w ⟨GateOp.or, [cur, a]⟩
    have hlen1 : w1.length = base + 1 := by simp [w1, stepWire, hlen]
    have hrest : ∀ u ∈ rest, u < base + 1 := fun u hu => Nat.lt_succ_of_lt (hws u (by simp [hu]))
    rw [ih (base + 1) base w1 hlen1 (Nat.lt_succ_self base) hrest]
    have hcur1 : w1.getD base false = (w.getD cur false || w.getD a false) := by
      have : w1 = w ++ [w.getD cur false || w.getD a false] := by simp [w1, stepWire, GateOp.eval]
      rw [this, ← hlen, getD_singleton_last]
    have hany : rest.any (fun u => w1.getD u false) = rest.any (fun u => w.getD u false) := by
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true]
      exact exists_congr fun u => and_congr_right fun hu => by
        have hu' : u < w.length := hlen.symm ▸ hws u (by simp [hu])
        dsimp only [w1, stepWire]
        rw [getD_append_left w _ false hu']
    rw [hcur1, hany, Bool.or_assoc]

lemma chainAux_eval_and (base cur : Nat) (ws : List Nat) (w : List Bool)
    (hlen : w.length = base) (hcur : cur < base) (hws : ∀ u ∈ ws, u < base) :
    ((chainAux GateOp.and base cur ws).1.foldl stepWire w).getD (chainAux GateOp.and base cur ws).2 false =
    (w.getD cur false && ws.all (fun u => w.getD u false)) := by
  induction ws generalizing base cur w with
  | nil => simp [chainAux]
  | cons a rest ih =>
    simp only [chainAux, List.foldl_cons, List.all_cons]
    let w1 := stepWire w ⟨GateOp.and, [cur, a]⟩
    have hlen1 : w1.length = base + 1 := by simp [w1, stepWire, hlen]
    have hrest : ∀ u ∈ rest, u < base + 1 := fun u hu => Nat.lt_succ_of_lt (hws u (by simp [hu]))
    rw [ih (base + 1) base w1 hlen1 (Nat.lt_succ_self base) hrest]
    have hcur1 : w1.getD base false = (w.getD cur false && w.getD a false) := by
      have : w1 = w ++ [w.getD cur false && w.getD a false] := by simp [w1, stepWire, GateOp.eval]
      rw [this, ← hlen, getD_singleton_last]
    have hall : rest.all (fun u => w1.getD u false) = rest.all (fun u => w.getD u false) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      exact forall_congr' fun u => imp_congr_right fun hu => by
        have hu' : u < w.length := hlen.symm ▸ hws u (by simp [hu])
        dsimp only [w1, stepWire]
        rw [getD_append_left w _ false hu']
    rw [hcur1, hall, Bool.and_assoc]

def orList (base falseW : Nat) : List Nat → List Gate × Nat
  | [] => ([], falseW)
  | a :: rest => chainAux GateOp.or base a rest

def andList (base trueW : Nat) : List Nat → List Gate × Nat
  | [] => ([], trueW)
  | a :: rest => chainAux GateOp.and base a rest

lemma orList_len (base falseW : Nat) (ws : List Nat) : (orList base falseW ws).1.length ≤ ws.length := by
  cases ws with
  | nil => simp [orList]
  | cons a rest => simp [orList, chainAux_length]

lemma andList_len (base trueW : Nat) (ws : List Nat) : (andList base trueW ws).1.length ≤ ws.length := by
  cases ws with
  | nil => simp [andList]
  | cons a rest => simp [andList, chainAux_length]

lemma orList_spec (base falseW : Nat) (ws : List Nat)
    (hf : falseW < base) (hws : ∀ u ∈ ws, u < base) :
    ValidPos base (orList base falseW ws).1 ∧
    (orList base falseW ws).2 < base + (orList base falseW ws).1.length ∧
    ∀ (w : List Bool), w.length = base → w.getD falseW false = false →
      ((orList base falseW ws).1.foldl stepWire w).getD (orList base falseW ws).2 false =
      ws.any (fun u => w.getD u false) := by
  cases ws with
  | nil =>
    refine ⟨⟨by simp [orList], by simp [orList]⟩, by simpa [orList] using hf, fun w _ hfw => by simpa [orList] using hfw⟩
  | cons a rest =>
    refine ⟨chainAux_valid GateOp.or (Or.inr rfl) base a rest (hws a (by simp)) (fun u hu => hws u (by simp [hu])),
      by rw [orList, chainAux_length]; exact chainAux_out_lt GateOp.or base a rest (hws a (by simp)),
      fun w hlen _ => ?_⟩
    simpa [orList] using chainAux_eval_or base a rest w hlen (hws a (by simp)) (fun u hu => hws u (by simp [hu]))

lemma andList_spec (base trueW : Nat) (ws : List Nat)
    (ht : trueW < base) (hws : ∀ u ∈ ws, u < base) :
    ValidPos base (andList base trueW ws).1 ∧
    (andList base trueW ws).2 < base + (andList base trueW ws).1.length ∧
    ∀ (w : List Bool), w.length = base → w.getD trueW false = true →
      ((andList base trueW ws).1.foldl stepWire w).getD (andList base trueW ws).2 false =
      ws.all (fun u => w.getD u false) := by
  cases ws with
  | nil =>
    refine ⟨⟨by simp [andList], by simp [andList]⟩, by simpa [andList] using ht, fun w _ htw => by simpa [andList] using htw⟩
  | cons a rest =>
    refine ⟨chainAux_valid GateOp.and (Or.inl rfl) base a rest (hws a (by simp)) (fun u hu => hws u (by simp [hu])),
      by rw [andList, chainAux_length]; exact chainAux_out_lt GateOp.and base a rest (hws a (by simp)),
      fun w hlen _ => ?_⟩
    simpa [andList] using chainAux_eval_and base a rest w hlen (hws a (by simp)) (fun u hu => hws u (by simp [hu]))

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
          simp only [hm, hj, ha, hb, ↓reduceIte, zero_add]
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

lemma finset_inter_closed {k : Nat} (Y : Finset (Finset (Fin k)))
    (hinter : ∀ A ∈ Y, ∀ B ∈ Y, A ∩ B ∈ Y)
    (T : Finset (Finset (Fin k))) (hTY : T ⊆ Y) (hTne : T.Nonempty) :
    ∃ L ∈ Y, ∀ j : Fin k, j ∈ L ↔ ∀ X ∈ T, j ∈ X := by
  classical
  induction T using Finset.induction_on with
  | empty => exact absurd hTne Finset.not_nonempty_empty
  | @insert X T hx ih =>
    by_cases hTe : T.Nonempty
    · obtain ⟨L, hLY, hL⟩ := ih (Finset.Subset.trans (Finset.subset_insert X T) hTY) hTe
      refine ⟨X ∩ L, hinter X (hTY (Finset.mem_insert_self X T)) L hLY, fun j => ?_⟩
      simp only [Finset.mem_inter, hL, Finset.mem_insert, forall_eq_or_imp]
    · rw [Finset.not_nonempty_iff_eq_empty] at hTe
      subst hTe
      exact ⟨X, hTY (Finset.mem_insert_self X ∅), fun j => by simp⟩

lemma finset_union_closed {k : Nat} (Y : Finset (Finset (Fin k)))
    (hunion : ∀ A ∈ Y, ∀ B ∈ Y, A ∪ B ∈ Y)
    (T : Finset (Finset (Fin k))) (hTY : T ⊆ Y) (hTne : T.Nonempty) :
    ∃ U ∈ Y, ∀ j : Fin k, j ∈ U ↔ ∃ X ∈ T, j ∈ X := by
  classical
  induction T using Finset.induction_on with
  | empty => exact absurd hTne Finset.not_nonempty_empty
  | @insert X T hx ih =>
    by_cases hTe : T.Nonempty
    · obtain ⟨U, hUY, hU⟩ := ih (Finset.Subset.trans (Finset.subset_insert X T) hTY) hTe
      refine ⟨X ∪ U, hunion X (hTY (Finset.mem_insert_self X T)) U hUY, fun j => ?_⟩
      simp only [Finset.mem_union, hU, Finset.mem_insert, exists_eq_or_imp]
    · rw [Finset.not_nonempty_iff_eq_empty] at hTe
      subst hTe
      exact ⟨X, hTY (Finset.mem_insert_self X ∅), fun j => by simp⟩

lemma birkhoff_sublattice {k : Nat} (Y : Finset (Finset (Fin k)))
    (hne : Y.Nonempty)
    (hinter : ∀ A ∈ Y, ∀ B ∈ Y, A ∩ B ∈ Y)
    (hunion : ∀ A ∈ Y, ∀ B ∈ Y, A ∪ B ∈ Y)
    (W : Finset (Fin k))
    (hC1 : ∀ i : Fin k, (∀ X ∈ Y, i ∈ X) → i ∈ W)
    (hC0 : ∀ i : Fin k, (∀ X ∈ Y, i ∉ X) → i ∉ W)
    (hImp : ∀ i j : Fin k, (∀ X ∈ Y, i ∈ X → j ∈ X) → i ∈ W → j ∈ W) :
    W ∈ Y := by
  classical
  obtain ⟨Lmin, hLminY, hLmin⟩ := finset_inter_closed Y hinter Y Finset.Subset.rfl hne
  have hLmin_sub : Lmin ⊆ W := fun i hi => hC1 i ((hLmin i).mp hi)
  have hLi : ∀ i ∈ W, ∃ L ∈ Y, i ∈ L ∧ L ⊆ W := by
    intro i hiW
    have hex : ∃ X ∈ Y, i ∈ X := by
      by_contra hall
      push Not at hall
      exact hC0 i hall hiW
    let Ti := Y.filter (fun X => i ∈ X)
    have hTine : Ti.Nonempty := by
      obtain ⟨X, hXY, hiX⟩ := hex
      exact ⟨X, Finset.mem_filter.mpr ⟨hXY, hiX⟩⟩
    obtain ⟨L, hLY, hL⟩ := finset_inter_closed Y hinter Ti (Finset.filter_subset _ Y) hTine
    refine ⟨L, hLY, (hL i).mpr (fun X hX => (Finset.mem_filter.mp hX).2), fun j hjL => ?_⟩
    apply hImp i j _ hiW
    intro X hXY hiX
    exact (hL j).mp hjL X (Finset.mem_filter.mpr ⟨hXY, hiX⟩)
  choose fL hfLY hfL_in hfL_sub using hLi
  let T : Finset (Finset (Fin k)) := insert Lmin (W.attach.image (fun i => fL i.1 i.2))
  have hTY : T ⊆ Y := by
    intro X hX
    rcases Finset.mem_insert.mp hX with rfl | hXimg
    · exact hLminY
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hXimg
      exact hfLY i.1 i.2
  obtain ⟨U, hUY, hU⟩ := finset_union_closed Y hunion T hTY ⟨Lmin, Finset.mem_insert_self _ _⟩
  have hUW : U = W := by
    ext j
    rw [hU j]
    constructor
    · rintro ⟨X, hXT, hjX⟩
      rcases Finset.mem_insert.mp hXT with rfl | hXimg
      · exact hLmin_sub hjX
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hXimg
        exact hfL_sub i.1 i.2 hjX
    · intro hjW
      exact ⟨fL j hjW, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨j, hjW⟩, Finset.mem_attach _ _, rfl⟩),
        hfL_in j hjW⟩
  rwa [← hUW]

lemma sublattice_feas_iff {k : Nat} (Y : Finset (Finset (Fin k)))
    (hne : Y.Nonempty)
    (hinter : ∀ A ∈ Y, ∀ B ∈ Y, A ∩ B ∈ Y)
    (hunion : ∀ A ∈ Y, ∀ B ∈ Y, A ∪ B ∈ Y)
    (P1 P0 : Finset (Fin k)) :
    (∃ W ∈ Y, W ⊆ P1 ∧ Finset.univ \ W ⊆ P0) ↔
    (∀ i : Fin k, i ∈ P1 ∨ i ∈ P0) ∧
    (∀ i : Fin k, (∀ X ∈ Y, i ∈ X) → i ∈ P1) ∧
    (∀ i : Fin k, (∀ X ∈ Y, i ∉ X) → i ∈ P0) ∧
    (∀ i j : Fin k, (∀ X ∈ Y, i ∈ X → j ∈ X) → i ∈ P0 ∨ j ∈ P1) := by
  classical
  constructor
  · rintro ⟨W, hWY, hW1, hW0⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i ∈ W
      · exact Or.inl (hW1 hi)
      · exact Or.inr (hW0 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩))
    · intro i hall; exact hW1 (hall W hWY)
    · intro i hall; exact hW0 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hall W hWY⟩)
    · intro i j himp
      by_cases hi : i ∈ W
      · exact Or.inr (hW1 (himp W hWY hi))
      · exact Or.inl (hW0 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩))
  · rintro ⟨hallP, hC1, hC0, hImp⟩
    let W : Finset (Fin k) := Finset.univ.filter fun j =>
      (∀ X ∈ Y, j ∈ X) ∨ ∃ i : Fin k, i ∉ P0 ∧ ∀ X ∈ Y, i ∈ X → j ∈ X
    have hWY : W ∈ Y := by
      apply birkhoff_sublattice Y hne hinter hunion W
      · intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl hi⟩
      · intro i hi0 hiW
        simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hiW
        rcases hiW with hi1 | ⟨a, ha0, haimp⟩
        · obtain ⟨X, hXY⟩ := hne
          exact hi0 X hXY (hi1 X hXY)
        · have ha_all0 : ∀ X ∈ Y, a ∉ X := fun X hXY haX => hi0 X hXY (haimp X hXY haX)
          exact ha0 (hC0 a ha_all0)
      · intro i j hij hiW
        simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hiW ⊢
        rcases hiW with hi1 | ⟨a, ha0, haimp⟩
        · exact Or.inl (fun X hXY => hij X hXY (hi1 X hXY))
        · exact Or.inr ⟨a, ha0, fun X hXY haX => hij X hXY (haimp X hXY haX)⟩
    refine ⟨W, hWY, ?_, ?_⟩
    · intro j hjW
      simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hjW
      rcases hjW with hj1 | ⟨a, ha0, haimp⟩
      · exact hC1 j hj1
      · exact (hImp a j haimp).resolve_left ha0
    · intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
      by_contra hi0
      apply hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr ⟨i, hi0, fun _ _ h => h⟩⟩

lemma sublattice_att1_iff {k : Nat} (Y : Finset (Finset (Fin k)))
    (hne : Y.Nonempty)
    (hinter : ∀ A ∈ Y, ∀ B ∈ Y, A ∩ B ∈ Y)
    (hunion : ∀ A ∈ Y, ∀ B ∈ Y, A ∪ B ∈ Y)
    (P1 P0 : Finset (Fin k)) (i0 : Fin k) :
    (∃ W ∈ Y, W ⊆ P1 ∧ Finset.univ \ W ⊆ P0 ∧ i0 ∈ W) ↔
    (∃ W ∈ Y, W ⊆ P1 ∧ Finset.univ \ W ⊆ P0) ∧
    (¬ ∀ X ∈ Y, i0 ∉ X) ∧
    (∀ j : Fin k, (∀ X ∈ Y, i0 ∈ X → j ∈ X) → j ∈ P1) := by
  classical
  constructor
  · rintro ⟨W, hWY, hW1, hW0, hi0⟩
    refine ⟨⟨W, hWY, hW1, hW0⟩, fun hall => hall W hWY hi0, fun j himp => hW1 (himp W hWY hi0)⟩
  · rintro ⟨⟨Wf, hWfY, hWf1, hWf0⟩, hnot0, hsucc⟩
    have hex : ∃ X ∈ Y, i0 ∈ X := by
      by_contra hall; push Not at hall; exact hnot0 hall
    let Ti := Y.filter (fun X => i0 ∈ X)
    have hTine : Ti.Nonempty := by
      obtain ⟨X, hXY, hiX⟩ := hex; exact ⟨X, Finset.mem_filter.mpr ⟨hXY, hiX⟩⟩
    obtain ⟨L, hLY, hL⟩ := finset_inter_closed Y hinter Ti (Finset.filter_subset _ Y) hTine
    refine ⟨Wf ∪ L, hunion Wf hWfY L hLY, ?_, ?_, ?_⟩
    · refine Finset.union_subset hWf1 ?_
      intro j hjL
      apply hsucc j
      intro X hXY hiX
      exact (hL j).mp hjL X (Finset.mem_filter.mpr ⟨hXY, hiX⟩)
    · intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or] at hj
      exact hWf0 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj.1⟩)
    · exact Finset.mem_union_right _ ((hL i0).mpr fun X hX => (Finset.mem_filter.mp hX).2)

lemma sublattice_att0_iff {k : Nat} (Y : Finset (Finset (Fin k)))
    (hne : Y.Nonempty)
    (hinter : ∀ A ∈ Y, ∀ B ∈ Y, A ∩ B ∈ Y)
    (hunion : ∀ A ∈ Y, ∀ B ∈ Y, A ∪ B ∈ Y)
    (P1 P0 : Finset (Fin k)) (i0 : Fin k) :
    (∃ W ∈ Y, W ⊆ P1 ∧ Finset.univ \ W ⊆ P0 ∧ i0 ∉ W) ↔
    (∃ W ∈ Y, W ⊆ P1 ∧ Finset.univ \ W ⊆ P0) ∧
    (¬ ∀ X ∈ Y, i0 ∈ X) ∧
    (∀ j : Fin k, (∀ X ∈ Y, j ∈ X → i0 ∈ X) → j ∈ P0) := by
  classical
  constructor
  · rintro ⟨W, hWY, hW1, hW0, hi0⟩
    refine ⟨⟨W, hWY, hW1, hW0⟩, fun hall => hi0 (hall W hWY), fun j himp => ?_⟩
    have hj : j ∉ W := fun hjW => hi0 (himp W hWY hjW)
    exact hW0 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩)
  · rintro ⟨⟨Wf, hWfY, hWf1, hWf0⟩, hnot1, hpred⟩
    have hex : ∃ X ∈ Y, i0 ∉ X := by
      by_contra hall; push Not at hall; exact hnot1 hall
    let Ti := Y.filter (fun X => i0 ∉ X)
    have hTine : Ti.Nonempty := by
      obtain ⟨X, hXY, hiX⟩ := hex; exact ⟨X, Finset.mem_filter.mpr ⟨hXY, hiX⟩⟩
    obtain ⟨U, hUY, hU⟩ := finset_union_closed Y hunion Ti (Finset.filter_subset _ Y) hTine
    refine ⟨Wf ∩ U, hinter Wf hWfY U hUY, Finset.Subset.trans Finset.inter_subset_left hWf1, ?_, ?_⟩
    · intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_inter, not_and_or] at hj
      rcases hj with hj1 | hj2
      · exact hWf0 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj1⟩)
      · apply hpred j
        intro X hXY hjX
        by_contra hi0X
        apply hj2
        exact (hU j).mpr ⟨X, Finset.mem_filter.mpr ⟨hXY, hi0X⟩, hjX⟩
    · intro hi0
      have hi0U := (Finset.mem_inter.mp hi0).2
      obtain ⟨X, hXT, hi0X⟩ := (hU i0).mp hi0U
      exact (Finset.mem_filter.mp hXT).2 hi0X

def buildSeqAnd (trueW : Nat) : Nat → List (List Nat) → List Gate × List Nat
  | _, [] => ([], [])
  | base, ws :: rest =>
    let r1 := andList base trueW ws
    let r2 := buildSeqAnd trueW (base + r1.1.length) rest
    (r1.1 ++ r2.1, r1.2 :: r2.2)

lemma buildSeqAnd_len (trueW base : Nat) (wss : List (List Nat)) :
    (buildSeqAnd trueW base wss).1.length ≤ (wss.map List.length).sum ∧
    (buildSeqAnd trueW base wss).2.length = wss.length := by
  induction wss generalizing base with
  | nil => simp [buildSeqAnd]
  | cons ws rest ih =>
    have h1 := andList_len base trueW ws
    have h2 := ih (base + (andList base trueW ws).1.length)
    simp only [buildSeqAnd, List.length_append, List.map_cons, List.sum_cons, List.length_cons]
    exact ⟨by omega, by omega⟩

lemma buildSeqAnd_spec (trueW base : Nat) (wss : List (List Nat))
    (ht : trueW < base) (hwss : ∀ ws ∈ wss, ∀ u ∈ ws, u < base) :
    ValidPos base (buildSeqAnd trueW base wss).1 ∧
    (∀ o ∈ (buildSeqAnd trueW base wss).2, o < base + (buildSeqAnd trueW base wss).1.length) ∧
    ∀ (w : List Bool), w.length = base → w.getD trueW false = true →
      ∀ idx < wss.length,
        ((buildSeqAnd trueW base wss).1.foldl stepWire w).getD
          ((buildSeqAnd trueW base wss).2.getD idx trueW) false =
        (wss.getD idx []).all (fun u => w.getD u false) := by
  induction wss generalizing base with
  | nil =>
    refine ⟨⟨by simp [buildSeqAnd], by simp [buildSeqAnd]⟩, by simp [buildSeqAnd], by simp⟩
  | cons ws rest ih =>
    have h1 := andList_spec base trueW ws ht (hwss ws (by simp))
    let r1 := andList base trueW ws
    have h2 := ih (base + r1.1.length) (Nat.lt_of_lt_of_le ht (Nat.le_add_right _ _))
      (fun ws' hws' u hu => Nat.lt_of_lt_of_le (hwss ws' (by simp [hws']) u hu) (Nat.le_add_right _ _))
    refine ⟨validPos_append h1.1 h2.1, ?_, ?_⟩
    · intro o ho
      simp only [buildSeqAnd, List.mem_cons, List.length_append] at ho ⊢
      rcases ho with rfl | ho2
      · exact Nat.lt_of_lt_of_le h1.2.1 (by omega)
      · have := h2.2.1 o ho2; dsimp only [r1] at this; omega
    · intro w hlen htw idx hidx
      simp only [buildSeqAnd, foldl_stepWire_append]
      let w1 := r1.1.foldl stepWire w
      have hlen1 : w1.length = base + r1.1.length := by simp [w1, foldl_stepWire_length, hlen]
      have htw1 : w1.getD trueW false = true := by rw [foldl_stepWire_prefix w r1.1 (by omega)]; exact htw
      cases idx with
      | zero =>
        change ((buildSeqAnd trueW (base + r1.1.length) rest).1.foldl stepWire w1).getD
          ((r1.2 :: (buildSeqAnd trueW (base + r1.1.length) rest).2).getD 0 trueW) false =
          ((ws :: rest).getD 0 []).all (fun u => w.getD u false)
        simp only [List.getD_cons_zero]
        rw [foldl_stepWire_prefix w1 _ (by rw [hlen1]; exact h1.2.1)]
        exact h1.2.2 w hlen htw
      | succ idx' =>
        change ((buildSeqAnd trueW (base + r1.1.length) rest).1.foldl stepWire w1).getD
          ((r1.2 :: (buildSeqAnd trueW (base + r1.1.length) rest).2).getD (idx' + 1) trueW) false =
          ((ws :: rest).getD (idx' + 1) []).all (fun u => w.getD u false)
        simp only [List.getD_cons_succ]
        have hrec := h2.2.2 w1 hlen1 htw1 idx' (by simp at hidx; omega)
        rw [hrec]
        rw [Bool.eq_iff_iff]
        simp only [List.all_eq_true]
        exact forall_congr' fun u => imp_congr_right fun hu => by
          have hmem : rest.getD idx' [] ∈ rest := by
            simp only [List.getD, List.getElem?_eq_getElem (by simp at hidx; omega : idx' < rest.length),
              Option.getD_some]
            exact List.getElem_mem _
          have hu' : u < w.length := hlen.symm ▸ hwss _ (List.mem_cons_of_mem ws hmem) u hu
          dsimp only [w1]
          rw [foldl_stepWire_prefix w r1.1 hu']

def buildSeqOr (falseW : Nat) : Nat → List (List Nat) → List Gate × List Nat
  | _, [] => ([], [])
  | base, ws :: rest =>
    let r1 := orList base falseW ws
    let r2 := buildSeqOr falseW (base + r1.1.length) rest
    (r1.1 ++ r2.1, r1.2 :: r2.2)

lemma buildSeqOr_len (falseW base : Nat) (wss : List (List Nat)) :
    (buildSeqOr falseW base wss).1.length ≤ (wss.map List.length).sum ∧
    (buildSeqOr falseW base wss).2.length = wss.length := by
  induction wss generalizing base with
  | nil => simp [buildSeqOr]
  | cons ws rest ih =>
    have h1 := orList_len base falseW ws
    have h2 := ih (base + (orList base falseW ws).1.length)
    simp only [buildSeqOr, List.length_append, List.map_cons, List.sum_cons, List.length_cons]
    exact ⟨by omega, by omega⟩

lemma buildSeqOr_spec (falseW base : Nat) (wss : List (List Nat))
    (hf : falseW < base) (hwss : ∀ ws ∈ wss, ∀ u ∈ ws, u < base) :
    ValidPos base (buildSeqOr falseW base wss).1 ∧
    (∀ o ∈ (buildSeqOr falseW base wss).2, o < base + (buildSeqOr falseW base wss).1.length) ∧
    ∀ (w : List Bool), w.length = base → w.getD falseW false = false →
      ∀ idx < wss.length,
        ((buildSeqOr falseW base wss).1.foldl stepWire w).getD
          ((buildSeqOr falseW base wss).2.getD idx falseW) false =
        (wss.getD idx []).any (fun u => w.getD u false) := by
  induction wss generalizing base with
  | nil =>
    refine ⟨⟨by simp [buildSeqOr], by simp [buildSeqOr]⟩, by simp [buildSeqOr], by simp⟩
  | cons ws rest ih =>
    have h1 := orList_spec base falseW ws hf (hwss ws (by simp))
    let r1 := orList base falseW ws
    have h2 := ih (base + r1.1.length) (Nat.lt_of_lt_of_le hf (Nat.le_add_right _ _))
      (fun ws' hws' u hu => Nat.lt_of_lt_of_le (hwss ws' (by simp [hws']) u hu) (Nat.le_add_right _ _))
    refine ⟨validPos_append h1.1 h2.1, ?_, ?_⟩
    · intro o ho
      simp only [buildSeqOr, List.mem_cons, List.length_append] at ho ⊢
      rcases ho with rfl | ho2
      · exact Nat.lt_of_lt_of_le h1.2.1 (by omega)
      · have := h2.2.1 o ho2; dsimp only [r1] at this; omega
    · intro w hlen hfw idx hidx
      simp only [buildSeqOr, foldl_stepWire_append]
      let w1 := r1.1.foldl stepWire w
      have hlen1 : w1.length = base + r1.1.length := by simp [w1, foldl_stepWire_length, hlen]
      have hfw1 : w1.getD falseW false = false := by rw [foldl_stepWire_prefix w r1.1 (by omega)]; exact hfw
      cases idx with
      | zero =>
        change ((buildSeqOr falseW (base + r1.1.length) rest).1.foldl stepWire w1).getD
          ((r1.2 :: (buildSeqOr falseW (base + r1.1.length) rest).2).getD 0 falseW) false =
          ((ws :: rest).getD 0 []).any (fun u => w.getD u false)
        simp only [List.getD_cons_zero]
        rw [foldl_stepWire_prefix w1 _ (by rw [hlen1]; exact h1.2.1)]
        exact h1.2.2 w hlen hfw
      | succ idx' =>
        change ((buildSeqOr falseW (base + r1.1.length) rest).1.foldl stepWire w1).getD
          ((r1.2 :: (buildSeqOr falseW (base + r1.1.length) rest).2).getD (idx' + 1) falseW) false =
          ((ws :: rest).getD (idx' + 1) []).any (fun u => w.getD u false)
        simp only [List.getD_cons_succ]
        have hrec := h2.2.2 w1 hlen1 hfw1 idx' (by simp at hidx; omega)
        rw [hrec]
        rw [Bool.eq_iff_iff]
        simp only [List.any_eq_true]
        exact exists_congr fun u => and_congr_right fun hu => by
          have hmem : rest.getD idx' [] ∈ rest := by
            simp only [List.getD, List.getElem?_eq_getElem (by simp at hidx; omega : idx' < rest.length),
              Option.getD_some]
            exact List.getElem_mem _
          have hu' : u < w.length := hlen.symm ▸ hwss _ (List.mem_cons_of_mem ws hmem) u hu
          dsimp only [w1]
          rw [foldl_stepWire_prefix w r1.1 hu']

lemma list_sum_le_mul {α : Type*} (l : List α) (f : α → Nat) (M : Nat) (h : ∀ x ∈ l, f x ≤ M) :
    (l.map f).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

lemma flatMap_range_getD {α : Type*} (d : α) (m : Nat) (n : Nat) (f : Nat → List α)
    (hf : ∀ t, (f t).length = m) (t : Nat) (ht : t < n) (r : Nat) (hr : r < m) :
    ((List.range n).flatMap f).getD (t * m + r) d = (f t).getD r d := by
  induction n with
  | zero => omega
  | succ n' ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hlen_pre : ((List.range n').flatMap f).length = n' * m := by
      rw [List.length_flatMap]
      have hmap : (List.range n').map (fun x => (f x).length) = List.replicate n' m := by
        apply List.ext_getElem
        · simp
        · intro a _ _; simp [hf]
      rw [hmap, List.sum_replicate, smul_eq_mul]
    by_cases hlt : t < n'
    · have hpos : t * m + r < n' * m := by nlinarith
      rw [getD_append_left _ _ d (by omega)]
      exact ih hlt
    · have ht_eq : t = n' := by omega
      subst ht_eq
      rw [List.getD, List.getElem?_append_right (by rw [hlen_pre]; omega), hlen_pre, Nat.add_sub_cancel_left]
      rfl

lemma famY_closed {k N : Nat}
    (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (p : Fin k → Fin N)
    (D S I O : Finset (Fin N))
    (hbip : ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)) (A : Finset (Fin N)) :
    let sel : Finset (Fin N) → Prop := fun C =>
      ((∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧ ∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C.sum w ≤ B.sum w) ∧
      I ⊆ C ∧ Disjoint O C
    let flipView : Finset (Fin N) → Finset (Fin k) := fun C =>
      Finset.univ.filter (fun i : Fin k => if p i ∈ S then p i ∈ C else p i ∉ C)
    let Y := (Finset.univ.filter (fun C : Finset (Fin N) => sel C ∧ C ∩ D = A)).image flipView
    (∀ X ∈ Y, ∀ Z ∈ Y, X ∩ Z ∈ Y) ∧ (∀ X ∈ Y, ∀ Z ∈ Y, X ∪ Z ∈ Y) := by
  classical
  intro sel flipView Y
  have hboth : ∀ X ∈ Y, ∀ Z ∈ Y, X ∩ Z ∈ Y ∧ X ∪ Z ∈ Y := by
    intro X hX Z hZ
    obtain ⟨C1, hC1, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨C2, hC2, rfl⟩ := Finset.mem_image.mp hZ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC1 hC2
    have hD : C1 ∩ D = C2 ∩ D := hC1.2.trans hC2.2.symm
    obtain ⟨M, J, hM_mem, hJ_mem, hM_opt, hJ_opt, hsub_M, hsub_J⟩ :=
      bipartite_MJ G w D S C1 C2 hbip hC1.1.1 hC2.1.1 hD
    have hMD : M ∩ D = A := by
      rw [← hC1.2]; ext x; simp only [Finset.mem_inter, hM_mem]
      constructor
      · rintro ⟨h1 | h2 | h3, hxD⟩
        · exact ⟨h1.2, hxD⟩
        · exact absurd hxD h2.1
        · exact absurd hxD h3.1
      · rintro ⟨hx1, hxD⟩; exact ⟨Or.inl ⟨hxD, hx1⟩, hxD⟩
    have hJD : J ∩ D = A := by
      rw [← hC1.2]; ext x; simp only [Finset.mem_inter, hJ_mem]
      constructor
      · rintro ⟨h1 | h2 | h3, hxD⟩
        · exact ⟨h1.2, hxD⟩
        · exact absurd hxD h2.1
        · exact absurd hxD h3.1
      · rintro ⟨hx1, hxD⟩; exact ⟨Or.inl ⟨hxD, hx1⟩, hxD⟩
    have hMsel : sel M := ⟨hM_opt,
      Finset.Subset.trans (Finset.subset_inter hC1.1.2.1 hC2.1.2.1) hsub_M.1,
      Finset.disjoint_of_subset_right hsub_M.2 (Finset.disjoint_union_right.mpr ⟨hC1.1.2.2, hC2.1.2.2⟩)⟩
    have hJsel : sel J := ⟨hJ_opt,
      Finset.Subset.trans (Finset.subset_inter hC1.1.2.1 hC2.1.2.1) hsub_J.1,
      Finset.disjoint_of_subset_right hsub_J.2 (Finset.disjoint_union_right.mpr ⟨hC1.1.2.2, hC2.1.2.2⟩)⟩
    have hD_iff : ∀ x ∈ D, x ∈ C1 ↔ x ∈ C2 := by
      intro x hxD; have h := Finset.ext_iff.mp hD x; simp [hxD] at h; exact h
    have hM_flip : flipView M = flipView C1 ∩ flipView C2 := by
      ext i; simp only [flipView, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hD1 : p i ∈ D
      · have hi := hD_iff (p i) hD1
        have hM1 : p i ∈ M ↔ p i ∈ C1 := by
          rw [hM_mem]; constructor
          · rintro (⟨_, h⟩ | ⟨hd, _⟩ | ⟨hd, _⟩); exact h; exact absurd hD1 hd; exact absurd hD1 hd
          · intro h; exact Or.inl ⟨hD1, h⟩
        split_ifs <;> tauto
      · by_cases hS1 : p i ∈ S
        · simp only [hS1, ↓reduceIte, hM_mem, hD1, false_and, false_or, not_false_eq_true, true_and, not_true_eq_false, or_false]
        · simp only [hS1, ↓reduceIte, hM_mem, hD1, false_and, false_or, not_false_eq_true, true_and, not_or]
    have hJ_flip : flipView J = flipView C1 ∪ flipView C2 := by
      ext i; simp only [flipView, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hD1 : p i ∈ D
      · have hi := hD_iff (p i) hD1
        have hJ1 : p i ∈ J ↔ p i ∈ C1 := by
          rw [hJ_mem]; constructor
          · rintro (⟨_, h⟩ | ⟨hd, _⟩ | ⟨hd, _⟩); exact h; exact absurd hD1 hd; exact absurd hD1 hd
          · intro h; exact Or.inl ⟨hD1, h⟩
        split_ifs <;> tauto
      · by_cases hS1 : p i ∈ S
        · simp only [hS1, ↓reduceIte, hJ_mem, hD1, false_and, false_or, not_false_eq_true, true_and, not_true_eq_false, or_false]
        · simp only [hS1, ↓reduceIte, hJ_mem, hD1, false_and, false_or, not_false_eq_true, true_and, not_and_or]
    exact ⟨Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ M, hMsel, hMD⟩, hM_flip⟩,
           Finset.mem_image.mpr ⟨J, Finset.mem_filter.mpr ⟨Finset.mem_univ J, hJsel, hJD⟩, hJ_flip⟩⟩
  exact ⟨fun X hX Z hZ => (hboth X hX Z hZ).1, fun X hX Z hZ => (hboth X hX Z hZ).2⟩

lemma main_circuit_construction {k N : Nat}
    (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (p : Fin k → Fin N)
    (D S I O : Finset (Fin N))
    (hbip : ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)) :
    ∃ (E : Circuit) (tap : Fin k → Bool → Nat),
      (FanInTwo E ∧ ReadsBack (2 * k + 2) E ∧ E.output < 2 * k + 2 + E.size ∧ PEqualNP.NotBracket.notCount E = 0) ∧
      E.size ≤ 12 * (k + 1) ^ 2 * 2 ^ D.card ∧
      (∀ i b, tap i b < 2 * k + 2 + E.size) ∧
      (∀ I1 O1 : Finset (Fin k),
        let x := List.ofFn (fun j : Fin k => decide (j ∈ I1)) ++
                 List.ofFn (fun j : Fin k => decide (j ∈ O1)) ++ [false, true]
        let ws := E.wires x
        let sel := fun C : Finset (Fin N) =>
          ((∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧ ∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C.sum w ≤ B.sum w) ∧
          I ⊆ C ∧ Disjoint O C
        let view := fun C : Finset (Fin N) => Finset.univ.filter (fun i : Fin k => p i ∈ C)
        (ws.getD E.output false = true ↔ ∃ C, sel C ∧ view C ⊆ I1 ∧ Finset.univ \ view C ⊆ O1) ∧
        ∀ i b, (ws.getD (tap i b) false = true ↔
          ∃ C, sel C ∧ view C ⊆ I1 ∧ Finset.univ \ view C ⊆ O1 ∧ decide (p i ∈ C) = b)) := by
  classical
  let sel : Finset (Fin N) → Prop := fun C =>
    ((∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧ ∀ B : Finset (Fin N), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C.sum w ≤ B.sum w) ∧
    I ⊆ C ∧ Disjoint O C
  let flipView : Finset (Fin N) → Finset (Fin k) := fun C =>
    Finset.univ.filter (fun i : Fin k => if p i ∈ S then p i ∈ C else p i ∉ C)
  let famY : Finset (Fin N) → Finset (Finset (Fin k)) := fun A =>
    (Finset.univ.filter (fun C : Finset (Fin N) => sel C ∧ C ∩ D = A)).image flipView
  have hfamY_closed : ∀ A : Finset (Fin N),
      (∀ X ∈ famY A, ∀ Y ∈ famY A, X ∩ Y ∈ famY A) ∧
      (∀ X ∈ famY A, ∀ Y ∈ famY A, X ∪ Y ∈ famY A) :=
    fun A => famY_closed G w p D S I O hbip A
  let falseW := 2 * k
  let trueW := 2 * k + 1
  let b0 := 2 * k + 2
  let perm1 : Fin k → Nat := fun i => if p i ∈ S then i.val else k + i.val
  let perm0 : Fin k → Nat := fun i => if p i ∈ S then k + i.val else i.val
  have hperm1_lt : ∀ i : Fin k, perm1 i < b0 := fun i => by dsimp only [perm1, b0]; split_ifs <;> omega
  have hperm0_lt : ∀ i : Fin k, perm0 i < b0 := fun i => by dsimp only [perm0, b0]; split_ifs <;> omega
  let pairsBit : List (List Nat) := List.ofFn (fun i : Fin k => [perm1 i, perm0 i])
  let rBit := buildSeqOr falseW b0 pairsBit
  let b1 := b0 + rBit.1.length
  let rAllPerm := andList b1 trueW rBit.2
  let b2 := b1 + rAllPerm.1.length
  let pairsImp : List (List Nat) :=
    (List.finRange k).flatMap (fun i => (List.finRange k).map (fun j => [perm0 i, perm1 j]))
  let rImp := buildSeqOr falseW b2 pairsImp
  let b3 := b2 + rImp.1.length
  let orImpWire : Fin k → Fin k → Nat := fun i j => rImp.2.getD (i.val * k + j.val) falseW
  let As : List (Finset (Fin N)) := D.powerset.toList
  have hAs_len : As.length = 2 ^ D.card := by
    simp [As, Finset.length_toList, Finset.card_powerset]
  let feasInputs : Finset (Fin N) → List Nat := fun A =>
    let Y := famY A
    if Y.Nonempty then
      rAllPerm.2 ::
      ((List.finRange k).filter (fun i => decide (∀ X ∈ Y, i ∈ X))).map perm1 ++
      ((List.finRange k).filter (fun i => decide (∀ X ∈ Y, i ∉ X))).map perm0 ++
      ((List.finRange k).flatMap (fun i =>
        ((List.finRange k).filter (fun j => decide (∀ X ∈ Y, i ∈ X → j ∈ X))).map (fun j => orImpWire i j)))
    else [falseW]
  let rFeas := buildSeqAnd trueW b3 (As.map feasInputs)
  let b4 := b3 + rFeas.1.length
  let feasWire : Nat → Nat := fun idx => rFeas.2.getD idx falseW
  let att1Inputs : Nat → Fin k → List Nat := fun idx i0 =>
    let A := As.getD idx ∅
    let Y := famY A
    if Y.Nonempty ∧ ¬ (∀ X ∈ Y, i0 ∉ X) then
      feasWire idx ::
      ((List.finRange k).filter (fun j => decide (∀ X ∈ Y, i0 ∈ X → j ∈ X))).map perm1
    else [falseW]
  let att0Inputs : Nat → Fin k → List Nat := fun idx i0 =>
    let A := As.getD idx ∅
    let Y := famY A
    if Y.Nonempty ∧ ¬ (∀ X ∈ Y, i0 ∈ X) then
      feasWire idx ::
      ((List.finRange k).filter (fun j => decide (∀ X ∈ Y, j ∈ X → i0 ∈ X))).map perm0
    else [falseW]
  let attAllInputs : List (List Nat) :=
    (List.range As.length).flatMap (fun idx =>
      (List.finRange k).map (fun i0 => att1Inputs idx i0) ++
      (List.finRange k).map (fun i0 => att0Inputs idx i0))
  let rAtt := buildSeqAnd trueW b4 attAllInputs
  let b5 := b4 + rAtt.1.length
  let att1Wire : Nat → Fin k → Nat := fun idx i0 => rAtt.2.getD (idx * (2 * k) + i0.val) falseW
  let att0Wire : Nat → Fin k → Nat := fun idx i0 => rAtt.2.getD (idx * (2 * k) + k + i0.val) falseW
  let outFeasList : List Nat := (List.range As.length).map feasWire
  let outTapList : Fin k → Bool → List Nat := fun i0 b =>
    (List.range As.length).map (fun idx =>
      if (if p i0 ∈ S then b else !b) then att1Wire idx i0 else att0Wire idx i0)
  let finalLists : List (List Nat) :=
    outFeasList ::
    ((List.finRange k).map (fun i0 => outTapList i0 true) ++
     (List.finRange k).map (fun i0 => outTapList i0 false))
  let rFinal := buildSeqOr falseW b5 finalLists
  let gsAll := rBit.1 ++ rAllPerm.1 ++ rImp.1 ++ rFeas.1 ++ rAtt.1 ++ rFinal.1
  let outWire := rFinal.2.getD 0 falseW
  let tap : Fin k → Bool → Nat := fun i0 b =>
    if b then rFinal.2.getD (1 + i0.val) falseW else rFinal.2.getD (1 + k + i0.val) falseW
  let E : Circuit := ⟨gsAll, outWire⟩
  have hrBit_sp := buildSeqOr_spec falseW b0 pairsBit (by dsimp only [falseW, b0]; omega) (by
    intro ws hws u hu
    simp only [pairsBit, List.mem_ofFn] at hws
    obtain ⟨i, rfl⟩ := hws
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact hperm1_lt i
    · exact hperm0_lt i)
  have hrAllPerm_sp := andList_spec b1 trueW rBit.2 (by dsimp only [b1, b0, trueW]; omega) hrBit_sp.2.1
  have hrImp_sp := buildSeqOr_spec falseW b2 pairsImp (by dsimp only [b2, b1, b0, falseW]; omega) (by
    intro ws hws u hu
    simp only [pairsImp, List.mem_flatMap, List.mem_map] at hws
    obtain ⟨i, _, j, _, rfl⟩ := hws
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · have := hperm0_lt i; dsimp only [b2, b1]; omega
    · have := hperm1_lt j; dsimp only [b2, b1]; omega)
  have horImp_lt : ∀ i j : Fin k, orImpWire i j < b3 := by
    intro i j
    dsimp only [orImpWire]
    by_cases hlt : i.val * k + j.val < rImp.2.length
    · have hmem : rImp.2.getD (i.val * k + j.val) falseW ∈ rImp.2 := by
        simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        exact List.getElem_mem _
      exact hrImp_sp.2.1 _ hmem
    · simp only [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
      dsimp only [b3, b2, b1, b0, falseW]; omega
  have hrFeas_sp := buildSeqAnd_spec trueW b3 (As.map feasInputs) (by dsimp only [b3, b2, b1, b0, trueW]; omega) (by
    intro ws hws u hu
    simp only [List.mem_map] at hws
    obtain ⟨A, _, rfl⟩ := hws
    dsimp only [feasInputs] at hu
    split_ifs at hu
    · simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap] at hu
      rcases hu with (((rfl | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩) | ⟨i, _, j, _, rfl⟩)
      · have := hrAllPerm_sp.2.1; dsimp only [b3, b2, rAllPerm] at *; omega
      · have := hperm1_lt i; dsimp only [b3, b2, b1]; omega
      · have := hperm0_lt i; dsimp only [b3, b2, b1]; omega
      · exact horImp_lt i j
    · simp only [List.mem_singleton] at hu; subst hu; dsimp only [b3, b2, b1, b0, falseW]; omega)
  have hfeasWire_lt : ∀ idx, feasWire idx < b4 := by
    intro idx
    dsimp only [feasWire]
    by_cases hlt : idx < rFeas.2.length
    · have hmem : rFeas.2.getD idx falseW ∈ rFeas.2 := by
        simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        exact List.getElem_mem _
      exact hrFeas_sp.2.1 _ hmem
    · simp only [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
      dsimp only [b4, b3, b2, b1, b0, falseW]; omega
  have hrAtt_sp := buildSeqAnd_spec trueW b4 attAllInputs (by dsimp only [b4, b3, b2, b1, b0, trueW]; omega) (by
    intro ws hws u hu
    simp only [attAllInputs, List.mem_flatMap, List.mem_append, List.mem_map] at hws
    obtain ⟨idx, _, ⟨i0, _, rfl⟩ | ⟨i0, _, rfl⟩⟩ := hws
    · dsimp only [att1Inputs] at hu
      split_ifs at hu
      · simp only [List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨j, _, rfl⟩
        · exact hfeasWire_lt idx
        · have := hperm1_lt j; dsimp only [b4, b3, b2, b1]; omega
      · simp only [List.mem_singleton] at hu; subst hu; dsimp only [b4, b3, b2, b1, b0, falseW]; omega
    · dsimp only [att0Inputs] at hu
      split_ifs at hu
      · simp only [List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨j, _, rfl⟩
        · exact hfeasWire_lt idx
        · have := hperm0_lt j; dsimp only [b4, b3, b2, b1]; omega
      · simp only [List.mem_singleton] at hu; subst hu; dsimp only [b4, b3, b2, b1, b0, falseW]; omega)
  have hatt1_lt : ∀ idx i0, att1Wire idx i0 < b5 := by
    intro idx i0; dsimp only [att1Wire]
    by_cases hlt : idx * (2 * k) + i0.val < rAtt.2.length
    · have hmem : rAtt.2.getD (idx * (2 * k) + i0.val) falseW ∈ rAtt.2 := by
        simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]; exact List.getElem_mem _
      exact hrAtt_sp.2.1 _ hmem
    · simp only [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
      dsimp only [b5, b4, b3, b2, b1, b0, falseW]; omega
  have hatt0_lt : ∀ idx i0, att0Wire idx i0 < b5 := by
    intro idx i0; dsimp only [att0Wire]
    by_cases hlt : idx * (2 * k) + k + i0.val < rAtt.2.length
    · have hmem : rAtt.2.getD (idx * (2 * k) + k + i0.val) falseW ∈ rAtt.2 := by
        simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]; exact List.getElem_mem _
      exact hrAtt_sp.2.1 _ hmem
    · simp only [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
      dsimp only [b5, b4, b3, b2, b1, b0, falseW]; omega
  have hrFinal_sp := buildSeqOr_spec falseW b5 finalLists (by dsimp only [b5, b4, b3, b2, b1, b0, falseW]; omega) (by
    intro ws hws u hu
    simp only [finalLists, List.mem_cons, List.mem_append, List.mem_map] at hws
    rcases hws with rfl | (⟨i0, _, rfl⟩ | ⟨i0, _, rfl⟩)
    · simp only [outFeasList, List.mem_map] at hu
      obtain ⟨idx, _, rfl⟩ := hu
      have := hfeasWire_lt idx; dsimp only [b5]; omega
    · simp only [outTapList, List.mem_map] at hu
      obtain ⟨idx, _, rfl⟩ := hu
      split_ifs <;> first | exact hatt1_lt idx i0 | exact hatt0_lt idx i0
    · simp only [outTapList, List.mem_map] at hu
      obtain ⟨idx, _, rfl⟩ := hu
      split_ifs <;> first | exact hatt1_lt idx i0 | exact hatt0_lt idx i0)
  have hvalid_all : ValidPos b0 gsAll := by
    have h12 := validPos_append hrBit_sp.1 hrAllPerm_sp.1
    have h123 : ValidPos b0 (rBit.1 ++ rAllPerm.1 ++ rImp.1) := by
      apply validPos_append h12
      have : b0 + (rBit.1 ++ rAllPerm.1).length = b2 := by simp [b2, b1, Nat.add_assoc]
      exact this ▸ hrImp_sp.1
    have h1234 : ValidPos b0 (rBit.1 ++ rAllPerm.1 ++ rImp.1 ++ rFeas.1) := by
      apply validPos_append h123
      have : b0 + (rBit.1 ++ rAllPerm.1 ++ rImp.1).length = b3 := by simp [b3, b2, b1, Nat.add_assoc]
      exact this ▸ hrFeas_sp.1
    have h12345 : ValidPos b0 (rBit.1 ++ rAllPerm.1 ++ rImp.1 ++ rFeas.1 ++ rAtt.1) := by
      apply validPos_append h1234
      have : b0 + (rBit.1 ++ rAllPerm.1 ++ rImp.1 ++ rFeas.1).length = b4 := by simp [b4, b3, b2, b1, Nat.add_assoc]
      exact this ▸ hrAtt_sp.1
    apply validPos_append h12345
    have : b0 + (rBit.1 ++ rAllPerm.1 ++ rImp.1 ++ rFeas.1 ++ rAtt.1).length = b5 := by simp [b5, b4, b3, b2, b1, Nat.add_assoc]
    exact this ▸ hrFinal_sp.1
  have hfinal_lt : ∀ idx, rFinal.2.getD idx falseW < 2 * k + 2 + E.size := by
    intro idx
    have hlenE : 2 * k + 2 + E.size = b5 + rFinal.1.length := by
      simp only [E, gsAll, Circuit.size, b5, b4, b3, b2, b1, b0, List.length_append]; omega
    rw [hlenE]
    by_cases hlt : idx < rFinal.2.length
    · have hmem : rFinal.2.getD idx falseW ∈ rFinal.2 := by
        simp only [List.getD, List.getElem?_eq_getElem hlt, Option.getD_some]; exact List.getElem_mem _
      exact hrFinal_sp.2.1 _ hmem
    · simp only [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none]
      dsimp only [b5, b4, b3, b2, b1, b0, falseW]; omega
  have hszE : E.size ≤ 12 * (k + 1) ^ 2 * 2 ^ D.card := by
    have h1 : rBit.1.length ≤ 2 * k := by
      have hlen := (buildSeqOr_len falseW b0 pairsBit).1
      have hsum : (pairsBit.map List.length).sum ≤ pairsBit.length * 2 :=
        list_sum_le_mul pairsBit List.length 2 (by
          intro ws hws; simp only [pairsBit, List.mem_ofFn] at hws; obtain ⟨i, rfl⟩ := hws; simp)
      have hplen : pairsBit.length = k := by simp [pairsBit]
      dsimp only [rBit] at *; omega
    have h2 : rAllPerm.1.length ≤ k := by
      have hlen := andList_len b1 trueW rBit.2
      have hrlen : rBit.2.length = k := by rw [(buildSeqOr_len falseW b0 pairsBit).2]; simp [pairsBit]
      dsimp only [rAllPerm] at *; omega
    have h3 : rImp.1.length ≤ 2 * k * k := by
      have hlen := (buildSeqOr_len falseW b2 pairsImp).1
      have hsum : (pairsImp.map List.length).sum ≤ pairsImp.length * 2 :=
        list_sum_le_mul pairsImp List.length 2 (by
          intro ws hws; simp only [pairsImp, List.mem_flatMap, List.mem_map] at hws
          obtain ⟨i, _, j, _, rfl⟩ := hws; simp)
      have hplen : pairsImp.length = k * k := by
        simp [pairsImp, List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul]
      dsimp only [rImp] at *; nlinarith
    have h4 : rFeas.1.length ≤ 2 ^ D.card * (1 + 2 * k + k * k) := by
      have hlen := (buildSeqAnd_len trueW b3 (As.map feasInputs)).1
      have hsum : ((As.map feasInputs).map List.length).sum ≤ (As.map feasInputs).length * (1 + 2 * k + k * k) :=
        list_sum_le_mul (As.map feasInputs) List.length (1 + 2 * k + k * k) (by
          intro ws hws
          obtain ⟨A, _, rfl⟩ := List.mem_map.mp hws
          dsimp only [feasInputs]
          split_ifs
          · simp only [List.length_cons, List.length_append, List.length_map]
            have hf1 : ((List.finRange k).filter (fun i => decide (∀ X ∈ famY A, i ∈ X))).length ≤ k :=
              le_trans (List.length_filter_le _ _) (by simp)
            have hf2 : ((List.finRange k).filter (fun i => decide (∀ X ∈ famY A, i ∉ X))).length ≤ k :=
              le_trans (List.length_filter_le _ _) (by simp)
            have hf3 : ((List.finRange k).flatMap (fun i =>
                ((List.finRange k).filter (fun j => decide (∀ X ∈ famY A, i ∈ X → j ∈ X))).map (fun j => orImpWire i j))).length ≤ k * k := by
              rw [List.length_flatMap]
              have := list_sum_le_mul (List.finRange k) (fun i =>
                (((List.finRange k).filter (fun j => decide (∀ X ∈ famY A, i ∈ X → j ∈ X))).map (fun j => orImpWire i j)).length) k (by
                  intro i _; simp only [List.length_map]; exact le_trans (List.length_filter_le _ _) (by simp))
              simpa using this
            omega
          · simp; omega)
      have hmlen : (As.map feasInputs).length = 2 ^ D.card := by simp [hAs_len]
      rw [hmlen] at hsum; dsimp only [rFeas] at *; omega
    have h5 : rAtt.1.length ≤ 2 ^ D.card * (2 * k * (k + 1)) := by
      have hlen := (buildSeqAnd_len trueW b4 attAllInputs).1
      have hsum : (attAllInputs.map List.length).sum ≤ attAllInputs.length * (k + 1) :=
        list_sum_le_mul attAllInputs List.length (k + 1) (by
          intro ws hws
          simp only [attAllInputs, List.mem_flatMap, List.mem_append, List.mem_map] at hws
          obtain ⟨idx, _, ⟨i0, _, rfl⟩ | ⟨i0, _, rfl⟩⟩ := hws
          · dsimp only [att1Inputs]; split_ifs
            · simp only [List.length_cons, List.length_map]
              have := le_trans (List.length_filter_le (p := fun j => decide (∀ X ∈ famY (As.getD idx ∅), i0 ∈ X → j ∈ X)) (l := List.finRange k)) (by simp : (List.finRange k).length ≤ k)
              omega
            · simp
          · dsimp only [att0Inputs]; split_ifs
            · simp only [List.length_cons, List.length_map]
              have := le_trans (List.length_filter_le (p := fun j => decide (∀ X ∈ famY (As.getD idx ∅), j ∈ X → i0 ∈ X)) (l := List.finRange k)) (by simp : (List.finRange k).length ≤ k)
              omega
            · simp)
      have halen : attAllInputs.length = 2 ^ D.card * (2 * k) := by
        simp only [attAllInputs, List.length_flatMap]
        have hfn : (List.range As.length).map (fun idx =>
            ((List.finRange k).map (fun i0 => att1Inputs idx i0) ++
             (List.finRange k).map (fun i0 => att0Inputs idx i0)).length) =
            List.replicate As.length (2 * k) := by
          apply List.ext_getElem
          · simp
          · intro idx h1 h2; simp; omega
        rw [hfn, List.sum_replicate, smul_eq_mul, hAs_len]
      rw [halen] at hsum
      dsimp only [rAtt] at *; nlinarith
    have h6 : rFinal.1.length ≤ (1 + 2 * k) * 2 ^ D.card := by
      have hlen := (buildSeqOr_len falseW b5 finalLists).1
      have hsum : (finalLists.map List.length).sum ≤ finalLists.length * 2 ^ D.card :=
        list_sum_le_mul finalLists List.length (2 ^ D.card) (by
          intro ws hws
          simp only [finalLists, List.mem_cons, List.mem_append, List.mem_map] at hws
          rcases hws with rfl | (⟨i0, _, rfl⟩ | ⟨i0, _, rfl⟩)
          · simp [outFeasList, hAs_len]
          · simp [outTapList, hAs_len]
          · simp [outTapList, hAs_len])
      have hflen : finalLists.length = 1 + 2 * k := by simp [finalLists]; omega
      rw [hflen] at hsum; dsimp only [rFinal] at *; omega
    have hpow : 1 ≤ 2 ^ D.card := Nat.one_le_two_pow
    simp only [E, gsAll, Circuit.size, List.length_append]
    nlinarith
  have hposE := validPos_to_pos E hvalid_all (hfinal_lt 0)
  refine ⟨E, tap, hposE, hszE, fun i b => by dsimp only [tap]; split_ifs <;> exact hfinal_lt _, ?_⟩
  intro I1 O1
  let x := List.ofFn (fun j : Fin k => decide (j ∈ I1)) ++
           List.ofFn (fun j : Fin k => decide (j ∈ O1)) ++ [false, true]
  have hx_len : x.length = b0 := by simp [x, b0]; omega
  have hx_f : x.getD falseW false = false := by
    dsimp only [x, falseW]
    rw [List.getD, List.getElem?_append_right (by simp; omega), List.length_append, List.length_ofFn, List.length_ofFn]
    have : 2 * k - (k + k) = 0 := by omega
    rw [this]; rfl
  have hx_t : x.getD trueW false = true := by
    dsimp only [x, trueW]
    rw [List.getD, List.getElem?_append_right (by simp; omega), List.length_append, List.length_ofFn, List.length_ofFn]
    have : 2 * k + 1 - (k + k) = 1 := by omega
    rw [this]; rfl
  have hx_i1 : ∀ j : Fin k, x.getD j.val false = decide (j ∈ I1) := by
    intro j; dsimp only [x]
    rw [List.append_assoc, List.getD, List.getElem?_append_left (by simp)]
    simp [j.isLt]
  have hx_o1 : ∀ j : Fin k, x.getD (k + j.val) false = decide (j ∈ O1) := by
    intro j; dsimp only [x]
    rw [List.getD, List.getElem?_append_left (by simp),
        List.getElem?_append_right (by simp), List.length_ofFn, Nat.add_sub_cancel_left]
    simp [j.isLt]
  let P1 : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => if p i ∈ S then i ∈ I1 else i ∈ O1)
  let P0 : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => if p i ∈ S then i ∈ O1 else i ∈ I1)
  have hx_p1 : ∀ i : Fin k, x.getD (perm1 i) false = decide (i ∈ P1) := by
    intro i; dsimp only [perm1]
    by_cases hS : p i ∈ S
    · simp only [hS, ↓reduceIte, hx_i1 i, P1, Finset.mem_filter, Finset.mem_univ, true_and]
    · simp only [hS, ↓reduceIte, hx_o1 i, P1, Finset.mem_filter, Finset.mem_univ, true_and]
  have hx_p0 : ∀ i : Fin k, x.getD (perm0 i) false = decide (i ∈ P0) := by
    intro i; dsimp only [perm0]
    by_cases hS : p i ∈ S
    · simp only [hS, ↓reduceIte, hx_o1 i, P0, Finset.mem_filter, Finset.mem_univ, true_and]
    · simp only [hS, ↓reduceIte, hx_i1 i, P0, Finset.mem_filter, Finset.mem_univ, true_and]
  have hfits_iff : ∀ C : Finset (Fin N),
      (Finset.univ.filter (fun i : Fin k => p i ∈ C) ⊆ I1 ∧
       Finset.univ \ Finset.univ.filter (fun i : Fin k => p i ∈ C) ⊆ O1) ↔
      (flipView C ⊆ P1 ∧ Finset.univ \ flipView C ⊆ P0) := by
    intro C
    simp only [Finset.subset_iff, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, flipView, P1, P0]
    constructor
    · rintro ⟨h1, h0⟩
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · by_cases hS : p i ∈ S
        · simp only [hS, ↓reduceIte] at hi ⊢; exact h1 hi
        · simp only [hS, ↓reduceIte] at hi ⊢; exact h0 hi
      · by_cases hS : p i ∈ S
        · simp only [hS, ↓reduceIte] at hi ⊢; exact h0 hi
        · simp only [hS, ↓reduceIte, not_not] at hi ⊢; exact h1 hi
    · rintro ⟨h1, h0⟩
      refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · by_cases hS : p i ∈ S
        · have := @h1 i (by simp only [hS, ↓reduceIte]; exact hi); simp only [hS, ↓reduceIte] at this; exact this
        · have := @h0 i (by simp only [hS, ↓reduceIte, not_not]; exact hi); simp only [hS, ↓reduceIte] at this; exact this
      · by_cases hS : p i ∈ S
        · have := @h0 i (by simp only [hS, ↓reduceIte]; exact hi); simp only [hS, ↓reduceIte] at this; exact this
        · have := @h1 i (by simp only [hS, ↓reduceIte]; exact hi); simp only [hS, ↓reduceIte] at this; exact this
  let w1 := rBit.1.foldl stepWire x
  let w2 := rAllPerm.1.foldl stepWire w1
  let w3 := rImp.1.foldl stepWire w2
  let w4 := rFeas.1.foldl stepWire w3
  let w5 := rAtt.1.foldl stepWire w4
  let w6 := rFinal.1.foldl stepWire w5
  have hw1_len : w1.length = b1 := by simp [w1, foldl_stepWire_length, hx_len, b1]
  have hw2_len : w2.length = b2 := by simp [w2, foldl_stepWire_length, hw1_len, b2]
  have hw3_len : w3.length = b3 := by simp [w3, foldl_stepWire_length, hw2_len, b3]
  have hw4_len : w4.length = b4 := by simp [w4, foldl_stepWire_length, hw3_len, b4]
  have hw5_len : w5.length = b5 := by simp [w5, foldl_stepWire_length, hw4_len, b5]
  have hx_w1 : ∀ u < b0, w1.getD u false = x.getD u false := fun u hu =>
    foldl_stepWire_prefix x rBit.1 (hx_len.symm ▸ hu)
  have hx_w2 : ∀ u < b0, w2.getD u false = x.getD u false := fun u hu => by
    rw [foldl_stepWire_prefix w1 rAllPerm.1 (by rw [hw1_len]; exact Nat.lt_of_lt_of_le hu (Nat.le_add_right _ _)), hx_w1 u hu]
  have hx_w3 : ∀ u < b0, w3.getD u false = x.getD u false := fun u hu => by
    rw [foldl_stepWire_prefix w2 rImp.1 (by rw [hw2_len]; exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hu (Nat.le_add_right _ _)) (Nat.le_add_right _ _)), hx_w2 u hu]
  have hx_w4 : ∀ u < b0, w4.getD u false = x.getD u false := fun u hu => by
    rw [foldl_stepWire_prefix w3 rFeas.1 (by rw [hw3_len]; exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hu (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)), hx_w3 u hu]
  have hx_w5 : ∀ u < b0, w5.getD u false = x.getD u false := fun u hu => by
    rw [foldl_stepWire_prefix w4 rAtt.1 (by rw [hw4_len]; exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hu (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)), hx_w4 u hu]
  have hfl_lt : falseW < b0 := by dsimp only [falseW, b0]; omega
  have htr_lt : trueW < b0 := by dsimp only [trueW, b0]; omega
  have hw_eq : E.wires x = w6 := by
    simp only [E, gsAll, Circuit.wires]
    change (rBit.1 ++ rAllPerm.1 ++ rImp.1 ++ rFeas.1 ++ rAtt.1 ++ rFinal.1).foldl stepWire x = w6
    simp only [foldl_stepWire_append, w1, w2, w3, w4, w5, w6]
  have hw1_bit : ∀ i : Fin k, w1.getD (rBit.2.getD i.val falseW) false = decide (i ∈ P1 ∨ i ∈ P0) := by
    intro i
    rw [hrBit_sp.2.2 x hx_len hx_f i.val (by simp only [pairsBit, List.length_ofFn]; exact i.isLt)]
    have hget : pairsBit.getD i.val [] = [perm1 i, perm0 i] := by
      simp [pairsBit, List.getD, i.isLt]
    rw [hget]
    simp only [List.any_cons, List.any_nil, Bool.or_false, hx_p1 i, hx_p0 i]
    exact Bool.eq_iff_iff.mpr (by simp)
  have hw2_all : w2.getD rAllPerm.2 false = decide (∀ i : Fin k, i ∈ P1 ∨ i ∈ P0) := by
    have ht1 : w1.getD trueW false = true := by
      rw [foldl_stepWire_prefix x rBit.1 (by dsimp only [trueW, b0] at *; omega)]; exact hx_t
    rw [hrAllPerm_sp.2.2 w1 hw1_len ht1]
    have hlen_bit : rBit.2.length = k := by rw [(buildSeqOr_len falseW b0 pairsBit).2]; simp [pairsBit]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro hall i
      have hmem : rBit.2.getD i.val falseW ∈ rBit.2 := by
        simp only [List.getD, List.getElem?_eq_getElem (by omega : i.val < rBit.2.length), Option.getD_some]
        exact List.getElem_mem _
      have := hall _ hmem
      rwa [hw1_bit i, decide_eq_true_eq] at this
    · intro hall u hu
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hu
      have hget : rBit.2[idx] = rBit.2.getD idx falseW := by simp [List.getD, hidx]
      rw [hget, hw1_bit ⟨idx, by omega⟩, decide_eq_true_eq]
      exact hall ⟨idx, by omega⟩
  have hw3_imp : ∀ i j : Fin k, w3.getD (orImpWire i j) false = decide (i ∈ P0 ∨ j ∈ P1) := by
    intro i j
    have hf2 : w2.getD falseW false = false := by
      rw [foldl_stepWire_prefix w1 rAllPerm.1 (by dsimp only [b1, b0, falseW] at *; omega),
          foldl_stepWire_prefix x rBit.1 (by dsimp only [b0, falseW] at *; omega)]; exact hx_f
    have hlt_ij : i.val * k + j.val < pairsImp.length := by
      have hplen : pairsImp.length = k * k := by
        simp only [pairsImp, List.length_flatMap]
        have hmap : (List.finRange k).map (fun i => ((List.finRange k).map (fun j => [perm0 i, perm1 j])).length) =
            List.replicate k k := by
          apply List.ext_getElem <;> simp
        rw [hmap, List.sum_replicate, smul_eq_mul]
      have hi : i.val + 1 ≤ k := i.isLt
      have hj : j.val < k := j.isLt
      rw [hplen]
      calc i.val * k + j.val < i.val * k + k := Nat.add_lt_add_left hj _
        _ = (i.val + 1) * k := by rw [Nat.succ_mul]
        _ ≤ k * k := Nat.mul_le_mul_right k hi
    dsimp only [orImpWire]
    rw [hrImp_sp.2.2 w2 hw2_len hf2 (i.val * k + j.val) hlt_ij]
    have hget : pairsImp.getD (i.val * k + j.val) [] = [perm0 i, perm1 j] := by
      have hflat : ∀ (n : Nat) (f : Fin n → Fin k → List Nat) (a : Fin n) (b : Fin k),
          ((List.finRange n).flatMap (fun i => (List.finRange k).map (fun j => f i j))).getD (a.val * k + b.val) [] = f a b := by
        intro n
        induction n with
        | zero => intro _ a; exact Fin.elim0 a
        | succ n' ih =>
          intro f a b
          rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
          cases a using Fin.cases with
          | zero =>
            simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add]
            rw [getD_append_left _ _ [] (by simp)]
            simp [List.getD, b.isLt]
          | succ a' =>
            simp only [Fin.val_succ]
            have hge : k ≤ (a'.val + 1) * k + b.val := by
              have : (a'.val + 1) * k = k + a'.val * k := by ring
              omega
            have hsub : (a'.val + 1) * k + b.val - k = a'.val * k + b.val := by
              have : (a'.val + 1) * k = k + a'.val * k := by ring
              omega
            have hlen0 : ((List.finRange k).map (fun j => f 0 j)).length = k := by simp
            rw [List.getD, List.getElem?_append_right (hlen0.symm ▸ hge), hlen0, hsub]
            exact ih (fun i j => f i.succ j) a' b
      exact hflat k (fun i j => [perm0 i, perm1 j]) i j
    rw [hget]
    have hp0 : w2.getD (perm0 i) false = decide (i ∈ P0) := by rw [hx_w2 _ (hperm0_lt i), hx_p0 i]
    have hp1 : w2.getD (perm1 j) false = decide (j ∈ P1) := by rw [hx_w2 _ (hperm1_lt j), hx_p1 j]
    simp only [List.any_cons, List.any_nil, Bool.or_false, hp0, hp1]
    exact Bool.eq_iff_iff.mpr (by simp)
  have hw4_feas : ∀ idx < As.length,
      w4.getD (feasWire idx) false = true ↔
      ∃ W ∈ famY (As.getD idx ∅), W ⊆ P1 ∧ Finset.univ \ W ⊆ P0 := by
    intro idx hidx
    have ht3 : w3.getD trueW false = true := by rw [hx_w3 _ htr_lt, hx_t]
    have hf3 : w3.getD falseW false = false := by rw [hx_w3 _ hfl_lt, hx_f]
    have hsp := hrFeas_sp.2.2 w3 hw3_len ht3 idx (by simp [hidx])
    have hget_map : (As.map feasInputs).getD idx [] = feasInputs (As.getD idx ∅) := by
      simp [List.getD, hidx]
    have hfw_eq : w4.getD (feasWire idx) false = (feasInputs (As.getD idx ∅)).all (fun u => w3.getD u false) := by
      have hlen_f : rFeas.2.length = As.length := by rw [(buildSeqAnd_len trueW b3 (As.map feasInputs)).2]; simp
      have hget_r : rFeas.2.getD idx falseW = rFeas.2.getD idx trueW := by
        simp only [List.getD, List.getElem?_eq_getElem (by omega : idx < rFeas.2.length), Option.getD_some]
      dsimp only [feasWire]; rw [hget_r, hsp, hget_map]
    rw [hfw_eq]
    let A := As.getD idx ∅
    let Y := famY A
    change List.all (feasInputs A) (fun u => w3.getD u false) = true ↔ ∃ W ∈ Y, W ⊆ P1 ∧ Finset.univ \ W ⊆ P0
    dsimp only [feasInputs]
    by_cases hne : Y.Nonempty
    · have hne' : (famY A).Nonempty := hne
      simp only [hne', ↓reduceIte, List.all_cons, List.all_append, Bool.and_eq_true, List.all_eq_true,
        List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, List.mem_flatMap]
      have hall_w3 : w3.getD rAllPerm.2 false = decide (∀ i : Fin k, i ∈ P1 ∨ i ∈ P0) := by
        rw [foldl_stepWire_prefix w2 rImp.1 (by rw [hw2_len]; exact hrAllPerm_sp.2.1), hw2_all]
      have hp1_w3 : ∀ i : Fin k, w3.getD (perm1 i) false = decide (i ∈ P1) := fun i => by
        rw [hx_w3 _ (hperm1_lt i), hx_p1 i]
      have hp0_w3 : ∀ i : Fin k, w3.getD (perm0 i) false = decide (i ∈ P0) := fun i => by
        rw [hx_w3 _ (hperm0_lt i), hx_p0 i]
      rw [sublattice_feas_iff Y hne (hfamY_closed A).1 (hfamY_closed A).2 P1 P0]
      constructor
      · rintro ⟨⟨⟨hA1, hA2⟩, hA3⟩, hA4⟩
        rw [hall_w3, decide_eq_true_eq] at hA1
        refine ⟨hA1, fun i hi => ?_, fun i hi => ?_, fun i j hij => ?_⟩
        · have := hA2 (perm1 i) ⟨i, hi, rfl⟩; rwa [hp1_w3 i, decide_eq_true_eq] at this
        · have := hA3 (perm0 i) ⟨i, hi, rfl⟩; rwa [hp0_w3 i, decide_eq_true_eq] at this
        · have := hA4 (orImpWire i j) ⟨i, ⟨j, hij, rfl⟩⟩; rwa [hw3_imp i j, decide_eq_true_eq] at this
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨⟨⟨by rw [hall_w3, decide_eq_true_eq]; exact h1, ?_⟩, ?_⟩, ?_⟩
        · rintro _ ⟨i, hi, rfl⟩; rw [hp1_w3 i, decide_eq_true_eq]; exact h2 i hi
        · rintro _ ⟨i, hi, rfl⟩; rw [hp0_w3 i, decide_eq_true_eq]; exact h3 i hi
        · rintro _ ⟨i, j, hij, rfl⟩; rw [hw3_imp i j, decide_eq_true_eq]; exact h4 i j hij
    · have hne' : ¬ (famY A).Nonempty := hne
      simp only [hne', ↓reduceIte, List.all_cons, List.all_nil, Bool.and_true, hf3, Bool.false_eq_true, false_iff]
      rintro ⟨W, hWY, _⟩
      exact hne ⟨W, hWY⟩
  have hw5_att : ∀ idx < As.length, ∀ i0 : Fin k,
      (w5.getD (att1Wire idx i0) false = true ↔ ∃ W ∈ famY (As.getD idx ∅), W ⊆ P1 ∧ Finset.univ \ W ⊆ P0 ∧ i0 ∈ W) ∧
      (w5.getD (att0Wire idx i0) false = true ↔ ∃ W ∈ famY (As.getD idx ∅), W ⊆ P1 ∧ Finset.univ \ W ⊆ P0 ∧ i0 ∉ W) := by
    intro idx hidx i0
    have ht4 : w4.getD trueW false = true := by rw [hx_w4 _ htr_lt, hx_t]
    have hf4 : w4.getD falseW false = false := by rw [hx_w4 _ hfl_lt, hx_f]
    have hp1_w4 : ∀ j : Fin k, w4.getD (perm1 j) false = decide (j ∈ P1) := fun j => by
      rw [hx_w4 _ (hperm1_lt j), hx_p1 j]
    have hp0_w4 : ∀ j : Fin k, w4.getD (perm0 j) false = decide (j ∈ P0) := fun j => by
      rw [hx_w4 _ (hperm0_lt j), hx_p0 j]
    let fAtt : Nat → List (List Nat) := fun idx =>
      (List.finRange k).map (fun i0 => att1Inputs idx i0) ++
      (List.finRange k).map (fun i0 => att0Inputs idx i0)
    have hfAtt_len : ∀ t, (fAtt t).length = 2 * k := fun t => by simp [fAtt]; omega
    have halen : attAllInputs.length = As.length * (2 * k) := by
      simp only [attAllInputs, List.length_flatMap]
      have hfn : (List.range As.length).map (fun idx => (fAtt idx).length) =
          List.replicate As.length (2 * k) := by
        apply List.ext_getElem; · simp
        · intro a _ _; simp [hfAtt_len]
      change ((List.range As.length).map (fun idx => (fAtt idx).length)).sum = _
      rw [hfn, List.sum_replicate, smul_eq_mul]
    have hrAtt_len : rAtt.2.length = attAllInputs.length := (buildSeqAnd_len trueW b4 attAllInputs).2
    let A := As.getD idx ∅
    let Y := famY A
    constructor
    · have hpos1 : idx * (2 * k) + i0.val < attAllInputs.length := by
        rw [halen]
        calc idx * (2 * k) + i0.val < idx * (2 * k) + 2 * k := by omega
          _ = (idx + 1) * (2 * k) := by rw [← Nat.succ_mul]
          _ ≤ As.length * (2 * k) := Nat.mul_le_mul_right (2 * k) (Nat.succ_le_of_lt hidx)
      have hget_r : rAtt.2.getD (idx * (2 * k) + i0.val) falseW = rAtt.2.getD (idx * (2 * k) + i0.val) trueW := by
        simp only [List.getD, List.getElem?_eq_getElem (by omega : idx * (2 * k) + i0.val < rAtt.2.length), Option.getD_some]
      have hget1 : attAllInputs.getD (idx * (2 * k) + i0.val) [] = att1Inputs idx i0 := by
        change ((List.range As.length).flatMap fAtt).getD (idx * (2 * k) + i0.val) [] = _
        rw [flatMap_range_getD [] (2 * k) As.length fAtt hfAtt_len idx hidx i0.val (by omega)]
        dsimp only [fAtt]
        rw [getD_append_left _ _ [] (by simp)]
        simp [List.getD, i0.isLt]
      dsimp only [att1Wire]
      rw [hget_r, hrAtt_sp.2.2 w4 hw4_len ht4 _ hpos1, hget1]
      dsimp only [att1Inputs]
      by_cases hcond : (famY (As.getD idx ∅)).Nonempty ∧ ¬ ∀ X ∈ famY (As.getD idx ∅), i0 ∉ X
      · rw [if_pos hcond]
        simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true,
          List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        rw [sublattice_att1_iff (famY (As.getD idx ∅)) hcond.1 (hfamY_closed (As.getD idx ∅)).1 (hfamY_closed (As.getD idx ∅)).2 P1 P0 i0]
        constructor
        · rintro ⟨hf, hs⟩
          refine ⟨(hw4_feas idx hidx).mp hf, hcond.2, fun j hj => ?_⟩
          have := hs (perm1 j) ⟨j, hj, rfl⟩; rwa [hp1_w4 j, decide_eq_true_eq] at this
        · rintro ⟨hf, _, hs⟩
          refine ⟨(hw4_feas idx hidx).mpr hf, ?_⟩
          rintro _ ⟨j, hj, rfl⟩; rw [hp1_w4 j, decide_eq_true_eq]; exact hs j hj
      · rw [if_neg hcond]
        simp only [List.all_cons, List.all_nil, Bool.and_true, hf4, Bool.false_eq_true, false_iff]
        rintro ⟨W, hWY, _, _, hi0W⟩
        exact hcond ⟨⟨W, hWY⟩, fun hall => hall W hWY hi0W⟩
    · have hpos0 : idx * (2 * k) + k + i0.val < attAllInputs.length := by
        rw [halen]
        calc idx * (2 * k) + k + i0.val < idx * (2 * k) + 2 * k := by omega
          _ = (idx + 1) * (2 * k) := by rw [← Nat.succ_mul]
          _ ≤ As.length * (2 * k) := Nat.mul_le_mul_right (2 * k) (Nat.succ_le_of_lt hidx)
      have hget_r : rAtt.2.getD (idx * (2 * k) + k + i0.val) falseW = rAtt.2.getD (idx * (2 * k) + k + i0.val) trueW := by
        simp only [List.getD, List.getElem?_eq_getElem (by omega : idx * (2 * k) + k + i0.val < rAtt.2.length), Option.getD_some]
      have hget0 : attAllInputs.getD (idx * (2 * k) + k + i0.val) [] = att0Inputs idx i0 := by
        have heq : idx * (2 * k) + k + i0.val = idx * (2 * k) + (k + i0.val) := by omega
        change ((List.range As.length).flatMap fAtt).getD (idx * (2 * k) + k + i0.val) [] = _
        rw [heq, flatMap_range_getD [] (2 * k) As.length fAtt hfAtt_len idx hidx (k + i0.val) (by omega)]
        dsimp only [fAtt]
        rw [List.getD, List.getElem?_append_right (by simp), List.length_map, List.length_finRange, Nat.add_sub_cancel_left]
        simp [i0.isLt]
      dsimp only [att0Wire]
      rw [hget_r, hrAtt_sp.2.2 w4 hw4_len ht4 _ hpos0, hget0]
      dsimp only [att0Inputs]
      by_cases hcond : (famY (As.getD idx ∅)).Nonempty ∧ ¬ ∀ X ∈ famY (As.getD idx ∅), i0 ∈ X
      · rw [if_pos hcond]
        simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true,
          List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        rw [sublattice_att0_iff (famY (As.getD idx ∅)) hcond.1 (hfamY_closed (As.getD idx ∅)).1 (hfamY_closed (As.getD idx ∅)).2 P1 P0 i0]
        constructor
        · rintro ⟨hf, hs⟩
          refine ⟨(hw4_feas idx hidx).mp hf, hcond.2, fun j hj => ?_⟩
          have := hs (perm0 j) ⟨j, hj, rfl⟩; rwa [hp0_w4 j, decide_eq_true_eq] at this
        · rintro ⟨hf, _, hs⟩
          refine ⟨(hw4_feas idx hidx).mpr hf, ?_⟩
          rintro _ ⟨j, hj, rfl⟩; rw [hp0_w4 j, decide_eq_true_eq]; exact hs j hj
      · rw [if_neg hcond]
        simp only [List.all_cons, List.all_nil, Bool.and_true, hf4, Bool.false_eq_true, false_iff]
        rintro ⟨W, hWY, _, _, hi0W⟩
        exact hcond ⟨⟨W, hWY⟩, fun hall => hi0W (hall W hWY)⟩
  have hf5 : w5.getD falseW false = false := by
    rw [foldl_stepWire_prefix w4 rAtt.1 (by dsimp only [b4, b3, b2, b1, b0, falseW] at *; omega),
        foldl_stepWire_prefix w3 rFeas.1 (by dsimp only [b3, b2, b1, b0, falseW] at *; omega),
        foldl_stepWire_prefix w2 rImp.1 (by dsimp only [b2, b1, b0, falseW] at *; omega),
        foldl_stepWire_prefix w1 rAllPerm.1 (by dsimp only [b1, b0, falseW] at *; omega),
        foldl_stepWire_prefix x rBit.1 (by dsimp only [b0, falseW] at *; omega)]; exact hx_f
  have hAs_mem : ∀ A : Finset (Fin N), A ∈ D.powerset ↔ ∃ idx < As.length, As.getD idx ∅ = A := by
    intro A
    rw [← Finset.mem_toList]
    constructor
    · intro hA
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hA
      exact ⟨idx, hidx, by simp only [As, List.getD, List.getElem?_eq_getElem hidx, Option.getD_some]⟩
    · rintro ⟨idx, hidx, rfl⟩
      simp only [As, List.getD, List.getElem?_eq_getElem hidx, Option.getD_some]
      exact List.getElem_mem _
  dsimp only
  rw [show E.wires _ = w6 from hw_eq]
  constructor
  · change w6.getD outWire false = true ↔ _
    dsimp only [outWire]
    rw [hrFinal_sp.2.2 w5 hw5_len hf5 0 (by simp [finalLists])]
    simp only [finalLists, List.getD_cons_zero, outFeasList, List.any_eq_true, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨_, ⟨idx, hidx, rfl⟩, htrue⟩
      rw [foldl_stepWire_prefix w4 rAtt.1 (by rw [hw4_len]; exact hfeasWire_lt idx)] at htrue
      obtain ⟨W, hWY, hW1, hW0⟩ := (hw4_feas idx hidx).mp htrue
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hWY
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      exact ⟨C, hC.1, (hfits_iff C).mpr ⟨hW1, hW0⟩⟩
    · rintro ⟨C, hCsel, hC1, hC0⟩
      obtain ⟨idx, hidx, hAeq⟩ := (hAs_mem (C ∩ D)).mp (Finset.mem_powerset.mpr Finset.inter_subset_right)
      refine ⟨feasWire idx, ⟨idx, hidx, rfl⟩, ?_⟩
      rw [foldl_stepWire_prefix w4 rAtt.1 (by rw [hw4_len]; exact hfeasWire_lt idx)]
      apply (hw4_feas idx hidx).mpr
      refine ⟨flipView C, Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_univ C, hCsel, hAeq.symm⟩, rfl⟩,
        (hfits_iff C).mp ⟨hC1, hC0⟩⟩
  · intro i0 b
    have htap_ev : w6.getD (tap i0 b) false = (outTapList i0 b).any (fun u => w5.getD u false) := by
      dsimp only [tap]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hrFinal_sp.2.2 w5 hw5_len hf5 (1 + k + i0.val) (by simp [finalLists]; omega)]
        simp only [finalLists]
        have hget : (outFeasList :: ((List.finRange k).map (fun i => outTapList i true) ++
            (List.finRange k).map (fun i => outTapList i false))).getD (1 + k + i0.val) [] = outTapList i0 false := by
          have : 1 + k + i0.val = (k + i0.val) + 1 := by omega
          rw [this, List.getD_cons_succ, List.getD, List.getElem?_append_right (by simp),
              List.length_map, List.length_finRange, Nat.add_sub_cancel_left]
          simp [i0.isLt]
        rw [hget]
      · simp only [↓reduceIte]
        rw [hrFinal_sp.2.2 w5 hw5_len hf5 (1 + i0.val) (by simp [finalLists]; omega)]
        simp only [finalLists]
        have hget : (outFeasList :: ((List.finRange k).map (fun i => outTapList i true) ++
            (List.finRange k).map (fun i => outTapList i false))).getD (1 + i0.val) [] = outTapList i0 true := by
          have : 1 + i0.val = i0.val + 1 := by omega
          rw [this, List.getD_cons_succ, getD_append_left _ _ [] (by simp)]
          simp [List.getD, i0.isLt]
        rw [hget]
    rw [htap_ev]
    simp only [outTapList, List.any_eq_true, List.mem_map, List.mem_range]
    have hflip_b : ∀ C : Finset (Fin N),
        decide (p i0 ∈ C) = b ↔
        (if (if p i0 ∈ S then b else !b) then i0 ∈ flipView C else i0 ∉ flipView C) := by
      intro C
      simp only [flipView, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hS : p i0 ∈ S <;> cases b <;> by_cases hC : p i0 ∈ C <;> simp [hS, hC]
    constructor
    · rintro ⟨_, ⟨idx, hidx, rfl⟩, htrue⟩
      by_cases hbit : (if p i0 ∈ S then b else !b) = true
      · rw [if_pos hbit] at htrue
        obtain ⟨W, hWY, hW1, hW0, hi0W⟩ := (hw5_att idx hidx i0).1.mp htrue
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hWY
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
        have ⟨h1, h0⟩ := (hfits_iff C).mpr ⟨hW1, hW0⟩
        exact ⟨C, hC.1, h1, h0, (hflip_b C).mpr (by rw [if_pos hbit]; exact hi0W)⟩
      · rw [if_neg hbit] at htrue
        obtain ⟨W, hWY, hW1, hW0, hi0W⟩ := (hw5_att idx hidx i0).2.mp htrue
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hWY
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
        have ⟨h1, h0⟩ := (hfits_iff C).mpr ⟨hW1, hW0⟩
        exact ⟨C, hC.1, h1, h0, (hflip_b C).mpr (by rw [if_neg hbit]; exact hi0W)⟩
    · rintro ⟨C, hCsel, hC1, hC0, hCb⟩
      obtain ⟨idx, hidx, hAeq⟩ := (hAs_mem (C ∩ D)).mp (Finset.mem_powerset.mpr Finset.inter_subset_right)
      have hWY : flipView C ∈ famY (As.getD idx ∅) :=
        Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_univ C, hCsel, hAeq.symm⟩, rfl⟩
      have ⟨hW1, hW0⟩ := (hfits_iff C).mp ⟨hC1, hC0⟩
      have hfb := (hflip_b C).mp hCb
      refine ⟨if (if p i0 ∈ S then b else !b) then att1Wire idx i0 else att0Wire idx i0, ⟨idx, hidx, rfl⟩, ?_⟩
      by_cases hbit : (if p i0 ∈ S then b else !b) = true
      · rw [if_pos hbit] at hfb ⊢
        exact (hw5_att idx hidx i0).1.mpr ⟨flipView C, hWY, hW1, hW0, hfb⟩
      · rw [if_neg hbit] at hfb ⊢
        exact (hw5_att idx hidx i0).2.mpr ⟨flipView C, hWY, hW1, hW0, hfb⟩

end PEqualNP.Outside.L_lib_1502_aux

theorem PEqualNP.Outside.L_lib_1502 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) D ∧ D.output < h+2+D.size
let pos := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => valid h D ∧ PEqualNP.NotBracket.notCount D=0
let cover := fun {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
let opt := fun {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (C : Finset (Fin N)) =>
  cover G C ∧ ∀ B, cover G B → C.sum w ≤ B.sum w
let bip := fun {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
let view := fun {k N : Nat} (p : Fin k → Fin N) (C : Finset (Fin N)) =>
  Finset.univ.filter (fun i => p i ∈ C)
let word := fun {k : Nat} (ones zeros : Finset (Fin k)) =>
  List.ofFn (fun j : Fin k => decide (j ∈ ones)) ++
  List.ofFn (fun j : Fin k => decide (j ∈ zeros)) ++ [false,true]
let fits := fun {k : Nat} (X I O : Finset (Fin k)) => X ⊆ I ∧ Finset.univ \ X ⊆ O
∀ (k N : Nat) (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (p : Fin k → Fin N)
  (D S I O : Finset (Fin N)), bip G D S →
let sel := fun (C : Finset (Fin N)) => opt G w C ∧ I ⊆ C ∧ Disjoint O C
∃ (E : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin k → Bool → Nat),
  pos (2*k) E ∧ E.size ≤ 12*(k+1)^2*2^D.card ∧
  (∀ i b, tap i b < 2*k+2+E.size) ∧
  (∀ I1 O1 : Finset (Fin k),
    let ws := E.wires (word I1 O1)
    (ws.getD E.output false=true ↔ ∃ C, sel C ∧ fits (view p C) I1 O1) ∧
    ∀ i b, (ws.getD (tap i b) false=true ↔
      ∃ C, sel C ∧ fits (view p C) I1 O1 ∧ decide (p i ∈ C)=b))) := by
  intro valid pos cover opt bip view word fits k N G w p D S I O hbip sel
  open PEqualNP.Outside.L_lib_1502_aux in
  obtain ⟨E, tap, hpos, hsz, htap_lt, heval⟩ := main_circuit_construction G w p D S I O hbip
  refine ⟨E, tap, ⟨⟨hpos.1, hpos.2.1, hpos.2.2.1⟩, hpos.2.2.2⟩, hsz, htap_lt, ?_⟩
  intro I1 O1
  obtain ⟨h1, h2⟩ := heval I1 O1
  have hword_eq : word I1 O1 =
      List.ofFn (fun j : Fin k => decide (j ∈ I1)) ++
      List.ofFn (fun j : Fin k => decide (j ∈ O1)) ++ [false, true] := by
    dsimp only [word]
    congr 2 <;> (apply List.ofFn_inj.mpr; funext j; exact decide_eq_decide.mpr Iff.rfl)
  constructor
  · rw [hword_eq, h1]
    dsimp only [fits, view, sel, opt, cover]
    constructor
    · rintro ⟨C, hC, hsub1, hsub0⟩
      exact ⟨C, hC, by convert hsub1, by convert hsub0⟩
    · rintro ⟨C, hC, hsub1, hsub0⟩
      exact ⟨C, hC, by convert hsub1, by convert hsub0⟩
  · intro i b
    rw [hword_eq, h2 i b]
    dsimp only [fits, view, sel, opt, cover]
    constructor
    · rintro ⟨C, hC, hsub1, hsub0, hb⟩
      exact ⟨C, hC, ⟨by convert hsub1, by convert hsub0⟩, by convert hb⟩
    · rintro ⟨C, hC, ⟨hsub1, hsub0⟩, hb⟩
      exact ⟨C, hC, by convert hsub1, by convert hsub0, by convert hb⟩
