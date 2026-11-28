import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1482

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.NotBracket
open Classical

section FoldAppend

def runFold {α β : Type*} (step : List α → β → α) (init : List α) (gs : List β) : List α :=
  gs.foldl (fun acc g => acc ++ [step acc g]) init

lemma runFold_nil {α β : Type*} (step : List α → β → α) (init : List α) :
    runFold step init [] = init := rfl

lemma runFold_cons {α β : Type*} (step : List α → β → α) (init : List α) (g : β) (gs : List β) :
    runFold step init (g :: gs) = runFold step (init ++ [step init g]) gs := rfl

lemma runFold_append {α β : Type*} (step : List α → β → α) (init : List α) (gs1 gs2 : List β) :
    runFold step init (gs1 ++ gs2) = runFold step (runFold step init gs1) gs2 := by
  simp [runFold, List.foldl_append]

lemma runFold_snoc {α β : Type*} (step : List α → β → α) (init : List α) (gs : List β) (g : β) :
    runFold step init (gs ++ [g]) =
      runFold step init gs ++ [step (runFold step init gs) g] := by
  rw [runFold_append]; rfl

lemma runFold_length {α β : Type*} (step : List α → β → α) (init : List α) (gs : List β) :
    (runFold step init gs).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [runFold]
  | cons g gs ih =>
    rw [runFold_cons, ih]
    simp
    omega

lemma runFold_getD_prefix {α β : Type*} (step : List α → β → α) (init : List α) (gs : List β)
    (i : ℕ) (d : α) (hi : i < init.length) :
    (runFold step init gs).getD i d = init.getD i d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    rw [runFold_cons]
    have hlt : i < (init ++ [step init g]).length := by simp; omega
    rw [ih (init ++ [step init g]) hlt]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma runFold_getD_append_left {α β : Type*} (step : List α → β → α) (init : List α)
    (gs1 gs2 : List β) (i : ℕ) (d : α) (hi : i < init.length + gs1.length) :
    (runFold step init (gs1 ++ gs2)).getD i d = (runFold step init gs1).getD i d := by
  rw [runFold_append, runFold_getD_prefix]
  rw [runFold_length]
  exact hi

lemma runFold_getD_gate {α β : Type*} (step : List α → β → α) (init : List α) (gs : List β)
    (t : ℕ) (d : α) (ht : t < gs.length) :
    (runFold step init gs).getD (init.length + t) d =
      step (runFold step init (gs.take t)) (gs[t]) := by
  have hsplit : gs = gs.take t ++ [gs[t]] ++ gs.drop (t + 1) := by
    have h1 := (List.take_append_drop t gs).symm
    have h2 : gs.drop t = gs[t] :: gs.drop (t + 1) := List.drop_eq_getElem_cons ht
    rw [h2] at h1
    rw [List.append_assoc]; exact h1
  have hlen : (gs.take t).length = t := List.length_take_of_le (Nat.le_of_lt ht)
  conv_lhs => rw [hsplit]
  rw [runFold_getD_append_left (gs1 := gs.take t ++ [gs[t]]) (gs2 := gs.drop (t + 1))
    (hi := by simp; omega)]
  rw [runFold_snoc]
  have heq : init.length + t = (runFold step init (gs.take t)).length := by
    rw [runFold_length, hlen]
  rw [heq]
  simp [List.getD_eq_getElem?_getD]

lemma runFold_getD_take {α β : Type*} (step : List α → β → α) (init : List α) (gs : List β)
    (t i : ℕ) (d : α) (ht : t ≤ gs.length) (hi : i < init.length + t) :
    (runFold step init (gs.take t)).getD i d = (runFold step init gs).getD i d := by
  have hlen : (gs.take t).length = t := List.length_take_of_le ht
  conv_rhs => rw [← List.take_append_drop t gs]
  rw [runFold_getD_append_left (hi := by rw [hlen]; exact hi)]

end FoldAppend

section BasicDefs

def valid (h : Nat) (D : Circuit) : Prop :=
  FanInTwo D ∧ ReadsBack (h + 2) D ∧ D.output < h + 2 + D.size

def pos (h : Nat) (D : Circuit) : Prop :=
  valid h D ∧ notCount D = 0

noncomputable def word {k : Nat} (ones zeros : Finset (Fin k)) : List Bool :=
  List.ofFn (fun j : Fin k => @decide (j ∈ ones) (Classical.propDecidable _)) ++
  List.ofFn (fun j : Fin k => @decide (j ∈ zeros) (Classical.propDecidable _)) ++ [false, true]

def wireInfo (k : Nat) (D : Circuit) : List (Finset (Fin k) × Finset (Fin k)) :=
  let Z : Finset (Fin k) × Finset (Fin k) := (∅, ∅)
  let xs := List.ofFn (fun j : Fin k => (({j}, ∅) : Finset (Fin k) × Finset (Fin k))) ++
    List.ofFn (fun j : Fin k => ((∅, {j}) : Finset (Fin k) × Finset (Fin k))) ++ [Z, Z]
  D.gates.foldl (fun (ts : List (Finset (Fin k) × Finset (Fin k))) g =>
    ts ++ [g.inputs.foldl (fun v t => let a := ts.getD t Z
                                      (v.1 ∪ a.1, v.2 ∪ a.2)) Z]) xs

def depths (h : Nat) (D : Circuit) : List Nat :=
  D.gates.foldl (fun (ts : List Nat) g =>
    ts ++ [1 + g.inputs.foldl (fun m j => max m (ts.getD j 0)) 0]) (List.replicate (h + 2) 0)

noncomputable def visInput {h : Nat} (Y : Finset (Fin h)) : List Bool :=
  List.ofFn (fun j : Fin h => @decide (j ∈ Y) (Classical.propDecidable _)) ++ [false, true]

lemma visInput_length {h : Nat} (Y : Finset (Fin h)) :
    (visInput Y).length = h + 2 := by
  simp [visInput]

lemma word_length {k : Nat} (ones zeros : Finset (Fin k)) :
    (word ones zeros).length = 2 * k + 2 := by
  simp [word]
  omega

lemma gateAt_eq {C : Circuit} {t : Nat} (ht : t < C.gates.length) :
    gateAt C t = C.gates[t] := by
  simp [gateAt, List.getD_eq_getElem?_getD, ht]

lemma gateAt_mem {C : Circuit} {t : Nat} (ht : t < C.gates.length) :
    gateAt C t ∈ C.gates := by
  rw [gateAt_eq ht]; exact List.getElem_mem ht

lemma notCount_zero_iff (C : Circuit) :
    notCount C = 0 ↔ ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  unfold notCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  simp

lemma pos_op {h : Nat} {D : Circuit} (hpos : pos h D) {g : Gate} (hg : g ∈ D.gates) :
    g.op = GateOp.and ∨ g.op = GateOp.or := by
  have hf := (hpos.1.1 g hg).1
  have hn := (notCount_zero_iff D).mp hpos.2 g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd h3 hn

lemma pos_len {h : Nat} {D : Circuit} (hpos : pos h D) {g : Gate} (hg : g ∈ D.gates) :
    g.inputs.length ≤ 2 :=
  (hpos.1.1 g hg).2

lemma wires_eq_runFold (C : Circuit) (x : List Bool) :
    C.wires x = runFold (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x C.gates := rfl

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size :=
  runFold_length _ x C.gates

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  runFold_getD_prefix _ x C.gates i false hi

lemma wires_getD_gate {n : Nat} {C : Circuit} (hRB : ReadsBack n C) {x : List Bool}
    (hx : x.length = n) {t : Nat} (ht : t < C.size) :
    (C.wires x).getD (n + t) false =
      (gateAt C t).op.eval ((gateAt C t).inputs.map fun i => (C.wires x).getD i false) := by
  rw [wires_eq_runFold, ← hx, runFold_getD_gate _ x C.gates t false ht, ← gateAt_eq ht]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt : i < x.length + t := by rw [hx]; exact hRB t ht i hi
  exact runFold_getD_take _ x C.gates t i false (Nat.le_of_lt ht) hlt

lemma depths_eq_runFold (h : Nat) (D : Circuit) :
    depths h D =
      runFold (fun ts g => 1 + g.inputs.foldl (fun m j => max m (ts.getD j 0)) 0)
        (List.replicate (h + 2) 0) D.gates := rfl

lemma depths_length (h : Nat) (D : Circuit) :
    (depths h D).length = h + 2 + D.size := by
  rw [depths_eq_runFold, runFold_length, List.length_replicate]; rfl

lemma depths_getD_input (h : Nat) (D : Circuit) (i : Nat) (hi : i < h + 2) :
    (depths h D).getD i 0 = 0 := by
  rw [depths_eq_runFold, runFold_getD_prefix _ _ _ i 0 (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi]

lemma depths_getD_gate {h : Nat} {D : Circuit} (hRB : ReadsBack (h + 2) D) {t : Nat}
    (ht : t < D.size) :
    (depths h D).getD (h + 2 + t) 0 =
      1 + (gateAt D t).inputs.foldl (fun m j => max m ((depths h D).getD j 0)) 0 := by
  rw [depths_eq_runFold]
  have hlen : (List.replicate (h + 2) 0).length = h + 2 := List.length_replicate
  have hstep := runFold_getD_gate (fun ts g => 1 + g.inputs.foldl (fun m j => max m (ts.getD j 0)) 0) (List.replicate (h + 2) 0) D.gates t 0 ht
  rw [hlen] at hstep
  rw [hstep, ← gateAt_eq ht]
  congr 1
  have hcong : ∀ (l : List Nat) (m : Nat), (∀ i ∈ l, i < h + 2 + t) →
      l.foldl (fun m j => max m ((runFold (fun ts g => 1 + g.inputs.foldl (fun m j => max m (ts.getD j 0)) 0)
        (List.replicate (h + 2) 0) (D.gates.take t)).getD j 0)) m =
      l.foldl (fun m j => max m ((runFold (fun ts g => 1 + g.inputs.foldl (fun m j => max m (ts.getD j 0)) 0)
        (List.replicate (h + 2) 0) D.gates).getD j 0)) m := by
    intro l
    induction l with
    | nil => intro m _; rfl
    | cons a as ih =>
      intro m hall
      simp only [List.foldl_cons]
      have ha : a < (List.replicate (h + 2) 0).length + t := by
        rw [hlen]; exact hall a (List.mem_cons_self ..)
      rw [runFold_getD_take _ _ D.gates t a 0 (Nat.le_of_lt ht) ha]
      exact ih _ (fun i hi => hall i (List.mem_cons_of_mem a hi))
  exact hcong _ 0 (fun i hi => hRB t ht i hi)

def infoInit (k : Nat) : List (Finset (Fin k) × Finset (Fin k)) :=
  let Z : Finset (Fin k) × Finset (Fin k) := (∅, ∅)
  List.ofFn (fun j : Fin k => (({j}, ∅) : Finset (Fin k) × Finset (Fin k))) ++
  List.ofFn (fun j : Fin k => ((∅, {j}) : Finset (Fin k) × Finset (Fin k))) ++ [Z, Z]

lemma infoInit_length (k : Nat) : (infoInit k).length = 2 * k + 2 := by
  simp [infoInit]
  omega

lemma wireInfo_eq_runFold (k : Nat) (D : Circuit) :
    wireInfo k D =
      runFold (fun ts g => g.inputs.foldl (fun v t =>
        let a := ts.getD t (∅, ∅); (v.1 ∪ a.1, v.2 ∪ a.2)) (∅, ∅))
        (infoInit k) D.gates := rfl

lemma wireInfo_getD_pos (k : Nat) (D : Circuit) (j : Fin k) :
    (wireInfo k D).getD j.val (∅, ∅) = ({j}, ∅) := by
  rw [wireInfo_eq_runFold, runFold_getD_prefix _ _ _ j.val _ (by rw [infoInit_length]; omega)]
  unfold infoInit
  rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [j.isLt])]
  simp [j.isLt]

lemma wireInfo_getD_neg (k : Nat) (D : Circuit) (j : Fin k) :
    (wireInfo k D).getD (k + j.val) (∅, ∅) = (∅, {j}) := by
  rw [wireInfo_eq_runFold, runFold_getD_prefix _ _ _ (k + j.val) _ (by rw [infoInit_length]; omega)]
  unfold infoInit
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp),
    List.getElem?_append_right (by simp)]
  simp [j.isLt]

lemma wireInfo_getD_const0 (k : Nat) (D : Circuit) :
    (wireInfo k D).getD (2 * k) (∅, ∅) = (∅, ∅) := by
  rw [wireInfo_eq_runFold, runFold_getD_prefix _ _ _ (2 * k) _ (by rw [infoInit_length]; omega)]
  unfold infoInit
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
  have h1 : 2 * k - (k + k) = 0 := by omega
  simp [h1]

lemma wireInfo_getD_const1 (k : Nat) (D : Circuit) :
    (wireInfo k D).getD (2 * k + 1) (∅, ∅) = (∅, ∅) := by
  rw [wireInfo_eq_runFold, runFold_getD_prefix _ _ _ (2 * k + 1) _ (by rw [infoInit_length]; omega)]
  unfold infoInit
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
  have h1 : 2 * k + 1 - (k + k) = 1 := by omega
  simp [h1]

lemma wireInfo_getD_gate {k : Nat} {D : Circuit} (hRB : ReadsBack (2 * k + 2) D) {t : Nat}
    (ht : t < D.size) :
    (wireInfo k D).getD (2 * k + 2 + t) (∅, ∅) =
      (gateAt D t).inputs.foldl (fun v u =>
        let a := (wireInfo k D).getD u (∅, ∅); (v.1 ∪ a.1, v.2 ∪ a.2)) (∅, ∅) := by
  rw [wireInfo_eq_runFold]
  have hlen : (infoInit k).length = 2 * k + 2 := infoInit_length k
  have hstep := runFold_getD_gate (fun ts g => g.inputs.foldl (fun v t => let a := ts.getD t (∅, ∅); (v.1 ∪ a.1, v.2 ∪ a.2)) (∅, ∅)) (infoInit k) D.gates t (∅, ∅) ht
  rw [hlen] at hstep
  rw [hstep, ← gateAt_eq ht]
  have hcong : ∀ (l : List Nat) (acc : Finset (Fin k) × Finset (Fin k)),
      (∀ i ∈ l, i < 2 * k + 2 + t) →
      l.foldl (fun v u => let a := (runFold (fun ts g => g.inputs.foldl (fun v t =>
        let a := ts.getD t (∅, ∅); (v.1 ∪ a.1, v.2 ∪ a.2)) (∅, ∅))
        (infoInit k) (D.gates.take t)).getD u (∅, ∅); (v.1 ∪ a.1, v.2 ∪ a.2)) acc =
      l.foldl (fun v u => let a := (runFold (fun ts g => g.inputs.foldl (fun v t =>
        let a := ts.getD t (∅, ∅); (v.1 ∪ a.1, v.2 ∪ a.2)) (∅, ∅))
        (infoInit k) D.gates).getD u (∅, ∅); (v.1 ∪ a.1, v.2 ∪ a.2)) acc := by
    intro l
    induction l with
    | nil => intro acc _; rfl
    | cons a as ih =>
      intro acc hall
      simp only [List.foldl_cons]
      have ha : a < (infoInit k).length + t := by
        rw [hlen]; exact hall a (List.mem_cons_self ..)
      rw [runFold_getD_take _ _ D.gates t a (∅, ∅) (Nat.le_of_lt ht) ha]
      exact ih _ (fun i hi => hall i (List.mem_cons_of_mem a hi))
  exact hcong _ (∅, ∅) (fun i hi => hRB t ht i hi)

lemma foldl_union_subset {k : Nat} (f : Nat → Finset (Fin k) × Finset (Fin k))
    (l : List Nat) (acc : Finset (Fin k) × Finset (Fin k)) :
    acc.1 ⊆ (l.foldl (fun v u => (v.1 ∪ (f u).1, v.2 ∪ (f u).2)) acc).1 ∧
    acc.2 ⊆ (l.foldl (fun v u => (v.1 ∪ (f u).1, v.2 ∪ (f u).2)) acc).2 ∧
    (∀ u ∈ l, (f u).1 ⊆ (l.foldl (fun v u => (v.1 ∪ (f u).1, v.2 ∪ (f u).2)) acc).1 ∧
              (f u).2 ⊆ (l.foldl (fun v u => (v.1 ∪ (f u).1, v.2 ∪ (f u).2)) acc).2) := by
  induction l generalizing acc with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (acc.1 ∪ (f a).1, acc.2 ∪ (f a).2)
    refine ⟨Finset.subset_union_left.trans h1, Finset.subset_union_left.trans h2, ?_⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact ⟨Finset.subset_union_right.trans h1, Finset.subset_union_right.trans h2⟩
    · exact h3 u hu'

lemma wireInfo_mono {k : Nat} {D : Circuit} (hRB : ReadsBack (2 * k + 2) D) {t : Nat}
    (ht : t < D.size) {u : Nat} (hu : u ∈ (gateAt D t).inputs) :
    ((wireInfo k D).getD u (∅, ∅)).1 ⊆ ((wireInfo k D).getD (2 * k + 2 + t) (∅, ∅)).1 ∧
    ((wireInfo k D).getD u (∅, ∅)).2 ⊆ ((wireInfo k D).getD (2 * k + 2 + t) (∅, ∅)).2 := by
  rw [wireInfo_getD_gate hRB ht]
  exact (foldl_union_subset (fun u => (wireInfo k D).getD u (∅, ∅))
    (gateAt D t).inputs (∅, ∅)).2.2 u hu

lemma word_getD_pos {k : Nat} (ones zeros : Finset (Fin k)) (j : Fin k) :
    (word ones zeros).getD j.val false = @decide (j ∈ ones) (Classical.propDecidable _) := by
  unfold word
  rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [j.isLt])]
  simp [j.isLt]

lemma word_getD_neg {k : Nat} (ones zeros : Finset (Fin k)) (j : Fin k) :
    (word ones zeros).getD (k + j.val) false = @decide (j ∈ zeros) (Classical.propDecidable _) := by
  unfold word
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp),
    List.getElem?_append_right (by simp)]
  simp [j.isLt]

lemma word_getD_const0 {k : Nat} (ones zeros : Finset (Fin k)) :
    (word ones zeros).getD (2 * k) false = false := by
  unfold word
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
  have h1 : 2 * k - (k + k) = 0 := by omega
  simp [h1]

lemma word_getD_const1 {k : Nat} (ones zeros : Finset (Fin k)) :
    (word ones zeros).getD (2 * k + 1) false = true := by
  unfold word
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
  have h1 : 2 * k + 1 - (k + k) = 1 := by omega
  simp [h1]

lemma visInput_getD_var {h : Nat} (Y : Finset (Fin h)) (j : Fin h) :
    (visInput Y).getD j.val false = @decide (j ∈ Y) (Classical.propDecidable _) := by
  unfold visInput
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [j.isLt])]
  simp [j.isLt]

lemma visInput_getD_const0 {h : Nat} (Y : Finset (Fin h)) :
    (visInput Y).getD h false = false := by
  unfold visInput
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

lemma visInput_getD_const1 {h : Nat} (Y : Finset (Fin h)) :
    (visInput Y).getD (h + 1) false = true := by
  unfold visInput
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

lemma eval_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {l1 l2 : List Bool} (hlen : l1.length = l2.length)
    (hle : ∀ i (hi1 : i < l1.length) (hi2 : i < l2.length), l1[i] = true → l2[i] = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    exact hle i (hlen ▸ hi) hi (h _ (List.getElem_mem (hlen ▸ hi)))
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    exact ⟨l2[i]'(hlen ▸ hi), List.getElem_mem _, hle i hi (hlen ▸ hi) hbi⟩

lemma wires_mono {m : Nat} {D : Circuit} (hpos : pos m D) {x y : List Bool}
    (hx : x.length = m + 2) (hy : y.length = m + 2)
    (hle : ∀ i < m + 2, x.getD i false = true → y.getD i false = true) :
    ∀ w < m + 2 + D.size, (D.wires x).getD w false = true → (D.wires y).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hval
    by_cases hin : w < m + 2
    · rw [wires_getD_input D x w (by omega)] at hval
      rw [wires_getD_input D y w (by omega)]
      exact hle w hin hval
    · obtain ⟨t, rfl⟩ : ∃ t, w = m + 2 + t := ⟨w - (m + 2), by omega⟩
      have ht : t < D.size := by omega
      rw [wires_getD_gate hpos.1.2.1 hx ht] at hval
      rw [wires_getD_gate hpos.1.2.1 hy ht]
      refine eval_mono (pos_op hpos (gateAt_mem ht)) (by simp) ?_ hval
      intro i hi1 hi2 hb
      simp only [List.getElem_map] at hb ⊢
      have hmem : (gateAt D t).inputs[i]'(by simpa using hi1) ∈ (gateAt D t).inputs :=
        List.getElem_mem _
      have hlt := hpos.1.2.1 t ht _ hmem
      exact ih _ hlt (by omega) hb

end BasicDefs

section Remap

def remapCircuit (D : Circuit) (ρ : Nat → Nat) : Circuit :=
  ⟨D.gates.map (fun g => ⟨g.op, g.inputs.map ρ⟩), 0⟩

lemma remapCircuit_size (D : Circuit) (ρ : Nat → Nat) :
    (remapCircuit D ρ).size = D.size := by
  simp [remapCircuit, Circuit.size]

lemma remapCircuit_gateAt (D : Circuit) (ρ : Nat → Nat) {t : Nat} (ht : t < D.size) :
    gateAt (remapCircuit D ρ) t = ⟨(gateAt D t).op, (gateAt D t).inputs.map ρ⟩ := by
  have ht' : t < (remapCircuit D ρ).gates.length := by simp [remapCircuit]; exact ht
  rw [gateAt_eq ht', gateAt_eq ht]
  simp only [remapCircuit, List.getElem_map]; rfl

lemma remapCircuit_pos {m1 m2 : Nat} {D : Circuit} (hpos : pos m1 D) (ρ : Nat → Nat)
    (hρ_in : ∀ j < m1 + 2, ρ j < m2 + 2)
    (hρ_gate : ∀ t < D.size, ρ (m1 + 2 + t) = m2 + 2 + t) :
    pos m2 (remapCircuit D ρ) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    simp only [remapCircuit, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact ⟨(hpos.1.1 g0 hg0).1, by simp [(hpos.1.1 g0 hg0).2]⟩
  · intro t ht w hw
    have ht0 : t < D.size := by simpa [remapCircuit, Circuit.size] using ht
    rw [remapCircuit_gateAt D ρ ht0] at hw
    simp only [List.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have hu_lt : u < m1 + 2 + t := hpos.1.2.1 t ht0 u hu
    by_cases hin : u < m1 + 2
    · have := hρ_in u hin; omega
    · obtain ⟨s, rfl⟩ : ∃ s, u = m1 + 2 + s := ⟨u - (m1 + 2), by omega⟩
      rw [hρ_gate s (by omega)]; omega
  · simp [remapCircuit]
  · rw [notCount_zero_iff]
    intro g hg
    simp only [remapCircuit, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact (notCount_zero_iff D).mp hpos.2 g0 hg0

lemma remapCircuit_wires {m1 m2 : Nat} {D : Circuit} (hpos : pos m1 D) (ρ : Nat → Nat)
    (hρ_in : ∀ j < m1 + 2, ρ j < m2 + 2)
    (hρ_gate : ∀ t < D.size, ρ (m1 + 2 + t) = m2 + 2 + t)
    {x1 x2 : List Bool} (hx1 : x1.length = m1 + 2) (hx2 : x2.length = m2 + 2)
    (hmatch : ∀ j < m1 + 2, x2.getD (ρ j) false = x1.getD j false) :
    ∀ w < m1 + 2 + D.size,
      ((remapCircuit D ρ).wires x2).getD (ρ w) false = (D.wires x1).getD w false := by
  have hpos2 := remapCircuit_pos hpos ρ hρ_in hρ_gate
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < m1 + 2
    · rw [wires_getD_input _ x2 (ρ w) (by rw [hx2]; exact hρ_in w hin),
        wires_getD_input _ x1 w (by omega)]
      exact hmatch w hin
    · obtain ⟨t, rfl⟩ : ∃ t, w = m1 + 2 + t := ⟨w - (m1 + 2), by omega⟩
      have ht : t < D.size := by omega
      have ht2 : t < (remapCircuit D ρ).size := by rw [remapCircuit_size]; exact ht
      rw [hρ_gate t ht, wires_getD_gate hpos2.1.2.1 hx2 ht2, wires_getD_gate hpos.1.2.1 hx1 ht,
        remapCircuit_gateAt D ρ ht]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt := hpos.1.2.1 t ht u hu
      exact ih u hu_lt (by omega)

lemma remapCircuit_depths {m1 m2 : Nat} {D : Circuit} (hpos : pos m1 D) (ρ : Nat → Nat)
    (hρ_in : ∀ j < m1 + 2, ρ j < m2 + 2)
    (hρ_gate : ∀ t < D.size, ρ (m1 + 2 + t) = m2 + 2 + t) :
    ∀ w < m1 + 2 + D.size,
      (depths m2 (remapCircuit D ρ)).getD (ρ w) 0 = (depths m1 D).getD w 0 := by
  have hpos2 := remapCircuit_pos hpos ρ hρ_in hρ_gate
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < m1 + 2
    · rw [depths_getD_input m2 _ (ρ w) (hρ_in w hin), depths_getD_input m1 _ w hin]
    · obtain ⟨t, rfl⟩ : ∃ t, w = m1 + 2 + t := ⟨w - (m1 + 2), by omega⟩
      have ht : t < D.size := by omega
      have ht2 : t < (remapCircuit D ρ).size := by rw [remapCircuit_size]; exact ht
      rw [hρ_gate t ht, depths_getD_gate hpos2.1.2.1 ht2, depths_getD_gate hpos.1.2.1 ht,
        remapCircuit_gateAt D ρ ht]
      congr 1
      have hfold : ∀ (l : List Nat) (m : Nat), (∀ u ∈ l, u < m1 + 2 + t) →
          (l.map ρ).foldl (fun m j => max m ((depths m2 (remapCircuit D ρ)).getD j 0)) m =
          l.foldl (fun m j => max m ((depths m1 D).getD j 0)) m := by
        intro l
        induction l with
        | nil => intro m _; rfl
        | cons a as ihl =>
          intro m hall
          simp only [List.map_cons, List.foldl_cons]
          have ha := hall a (List.mem_cons_self ..)
          rw [ih a ha (by omega)]
          exact ihl _ (fun u hu => hall u (List.mem_cons_of_mem a hu))
      exact hfold _ 0 (fun u hu => hpos.1.2.1 t ht u hu)

end Remap

section ZeroWidth

noncomputable def crossGate (k : Nat) (D : Circuit) (t : Nat) : Finset (Fin k) :=
  let Z : Finset (Fin k) × Finset (Fin k) := (∅, ∅)
  let info := wireInfo k D
  let g := gateAt D t
  let a := (g.inputs.head?.map (fun j => info.getD j Z)).getD Z
  let b := (g.inputs[1]?.map (fun j => info.getD j Z)).getD Z
  if g.op = GateOp.and then (a.1 ∩ b.2) ∪ (a.2 ∩ b.1) else ∅

lemma list_len_le_two_cases {α : Type*} (l : List α) (hl : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ (∃ a b, l = [a, b]) := by
  cases l with
  | nil => exact Or.inl rfl
  | cons a t =>
    cases t with
    | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
    | cons b t2 =>
      cases t2 with
      | nil => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
      | cons c t3 => simp at hl

lemma zeroCross_cert {k : Nat} {D : Circuit}
    (hpos : pos (2 * k) D) (hcross : ∀ t < D.size, crossGate k D t = ∅)
    (ones zeros : Finset (Fin k)) :
    ∀ w < 2 * k + 2 + D.size,
      (D.wires (word ones zeros)).getD w false = true →
      ∃ P N : Finset (Fin k),
        P ⊆ ((wireInfo k D).getD w (∅, ∅)).1 ∧
        N ⊆ ((wireInfo k D).getD w (∅, ∅)).2 ∧
        P ⊆ ones ∧ N ⊆ zeros ∧ Disjoint P N ∧
        ∀ X : Finset (Fin k), P ⊆ X → Disjoint N X →
          (D.wires (word X (Finset.univ \ X))).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hval
    by_cases h1 : w < k
    · let j : Fin k := ⟨w, h1⟩
      rw [wires_getD_input D _ w (by rw [word_length]; omega)] at hval
      change (word ones zeros).getD j.val false = true at hval
      rw [word_getD_pos ones zeros j, @decide_eq_true_eq _ (Classical.propDecidable _)] at hval
      have hj : j ∈ ones := hval
      refine ⟨{j}, ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [wireInfo_getD_pos k D j]
      · simp
      · simpa using hj
      · simp
      · simp
      · intro X hPX _
        have hjX : j ∈ X := hPX (Finset.mem_singleton_self j)
        rw [wires_getD_input D _ w (by rw [word_length]; omega)]
        change (word X (Finset.univ \ X)).getD j.val false = true
        rw [word_getD_pos X (Finset.univ \ X) j, @decide_eq_true_eq _ (Classical.propDecidable _)]
        exact hjX
    · by_cases h2 : w < 2 * k
      · let j : Fin k := ⟨w - k, by omega⟩
        have hwj : w = k + j.val := by simp [j]; omega
        rw [hwj, wires_getD_input D _ (k + j.val) (by rw [word_length]; omega)] at hval
        rw [word_getD_neg ones zeros j, @decide_eq_true_eq _ (Classical.propDecidable _)] at hval
        have hj : j ∈ zeros := hval
        refine ⟨∅, {j}, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp
        · rw [hwj, wireInfo_getD_neg k D j]
        · simp
        · simpa using hj
        · simp
        · intro X _ hNX
          have hjX : j ∉ X := Finset.disjoint_left.mp hNX (Finset.mem_singleton_self j)
          rw [hwj, wires_getD_input D _ (k + j.val) (by rw [word_length]; omega),
            word_getD_neg X (Finset.univ \ X) j, @decide_eq_true_eq _ (Classical.propDecidable _)]
          simp [hjX]
      · by_cases h3 : w = 2 * k
        · subst h3
          rw [wires_getD_input D _ (2 * k) (by rw [word_length]; omega),
            word_getD_const0] at hval
          cases hval
        · by_cases h4 : w = 2 * k + 1
          · subst h4
            refine ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp, ?_⟩
            intro X _ _
            rw [wires_getD_input D _ (2 * k + 1) (by rw [word_length]; omega),
              word_getD_const1]
          · obtain ⟨t, rfl⟩ : ∃ t, w = 2 * k + 2 + t := ⟨w - (2 * k + 2), by omega⟩
            have ht : t < D.size := by omega
            rw [wires_getD_gate hpos.1.2.1 (word_length ones zeros) ht] at hval
            have hop := pos_op hpos (gateAt_mem ht)
            have hlen := pos_len hpos (gateAt_mem ht)
            rcases list_len_le_two_cases (gateAt D t).inputs hlen with hin | ⟨u, hin⟩ | ⟨u, v, hin⟩
            · rcases hop with hop | hop
              · refine ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp, ?_⟩
                intro X _ _
                rw [wires_getD_gate hpos.1.2.1 (word_length X _) ht, hop, hin]
                rfl
              · rw [hop, hin] at hval; cases hval
            · have hu_mem : u ∈ (gateAt D t).inputs := by rw [hin]; simp
              have hu_lt : u < 2 * k + 2 + t := hpos.1.2.1 t ht u hu_mem
              have hvu : (D.wires (word ones zeros)).getD u false = true := by
                rcases hop with hop | hop <;> simpa [hop, hin, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil] using hval
              obtain ⟨P, N, hP, hN, hPo, hNz, hdisj, hX⟩ := ih u hu_lt (by omega) hvu
              have hmono := wireInfo_mono hpos.1.2.1 ht hu_mem
              refine ⟨P, N, hP.trans hmono.1, hN.trans hmono.2, hPo, hNz, hdisj, ?_⟩
              intro X hPX hNX
              rw [wires_getD_gate hpos.1.2.1 (word_length X _) ht]
              rcases hop with hop | hop <;> rw [hop, hin] <;> simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, hX X hPX hNX] <;> rfl
            · have hu_mem : u ∈ (gateAt D t).inputs := by rw [hin]; simp
              have hv_mem : v ∈ (gateAt D t).inputs := by rw [hin]; simp
              have hu_lt : u < 2 * k + 2 + t := hpos.1.2.1 t ht u hu_mem
              have hv_lt : v < 2 * k + 2 + t := hpos.1.2.1 t ht v hv_mem
              have hmu := wireInfo_mono hpos.1.2.1 ht hu_mem
              have hmv := wireInfo_mono hpos.1.2.1 ht hv_mem
              rcases hop with hop | hop
              · simp only [hop, hin, List.map_cons, List.map_nil, GateOp.eval,
                  List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at hval
                obtain ⟨P1, N1, hP1, hN1, hP1o, hN1z, hd1, hX1⟩ := ih u hu_lt (by omega) hval.1
                obtain ⟨P2, N2, hP2, hN2, hP2o, hN2z, hd2, hX2⟩ := ih v hv_lt (by omega) hval.2
                have hcr := hcross t ht
                simp only [crossGate, hop, hin, ↓reduceIte, List.head?_cons,
                  List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some,
                  Option.getD_some] at hcr
                have hd12 : Disjoint P1 N2 := by
                  rw [Finset.disjoint_left]
                  intro x hx1 hx2
                  have hmem : x ∈ (((wireInfo k D).getD u (∅, ∅)).1 ∩
                      ((wireInfo k D).getD v (∅, ∅)).2) ∪
                      (((wireInfo k D).getD u (∅, ∅)).2 ∩
                      ((wireInfo k D).getD v (∅, ∅)).1) :=
                    Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hP1 hx1, hN2 hx2⟩)
                  rw [hcr] at hmem
                  exact Finset.notMem_empty x hmem
                have hd21 : Disjoint P2 N1 := by
                  rw [Finset.disjoint_left]
                  intro x hx2 hx1
                  have hmem : x ∈ (((wireInfo k D).getD u (∅, ∅)).1 ∩
                      ((wireInfo k D).getD v (∅, ∅)).2) ∪
                      (((wireInfo k D).getD u (∅, ∅)).2 ∩
                      ((wireInfo k D).getD v (∅, ∅)).1) :=
                    Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hN1 hx1, hP2 hx2⟩)
                  rw [hcr] at hmem
                  exact Finset.notMem_empty x hmem
                refine ⟨P1 ∪ P2, N1 ∪ N2,
                  Finset.union_subset (hP1.trans hmu.1) (hP2.trans hmv.1),
                  Finset.union_subset (hN1.trans hmu.2) (hN2.trans hmv.2),
                  Finset.union_subset hP1o hP2o,
                  Finset.union_subset hN1z hN2z,
                  Finset.disjoint_union_left.mpr
                    ⟨Finset.disjoint_union_right.mpr ⟨hd1, hd12⟩,
                     Finset.disjoint_union_right.mpr ⟨hd21, hd2⟩⟩, ?_⟩
                intro X hPX hNX
                rw [wires_getD_gate hpos.1.2.1 (word_length X _) ht, hop, hin]
                have h1 := hX1 X (Finset.subset_union_left.trans hPX)
                  (Finset.disjoint_union_left.mp hNX).1
                have h2 := hX2 X (Finset.subset_union_right.trans hPX)
                  (Finset.disjoint_union_left.mp hNX).2
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, h1, h2]; rfl
              · simp only [hop, hin, List.map_cons, List.map_nil, GateOp.eval,
                  List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true] at hval
                rcases hval with hvu | hvv
                · obtain ⟨P, N, hP, hN, hPo, hNz, hd, hX⟩ := ih u hu_lt (by omega) hvu
                  refine ⟨P, N, hP.trans hmu.1, hN.trans hmu.2, hPo, hNz, hd, ?_⟩
                  intro X hPX hNX
                  rw [wires_getD_gate hpos.1.2.1 (word_length X _) ht, hop, hin]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hX X hPX hNX, Bool.true_or]
                · obtain ⟨P, N, hP, hN, hPo, hNz, hd, hX⟩ := ih v hv_lt (by omega) hvv
                  refine ⟨P, N, hP.trans hmv.1, hN.trans hmv.2, hPo, hNz, hd, ?_⟩
                  intro X hPX hNX
                  rw [wires_getD_gate hpos.1.2.1 (word_length X _) ht, hop, hin]
                  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hX X hPX hNX, Bool.or_false, Bool.or_true]

end ZeroWidth

section WidthCompile

def GoodGates (h : Nat) (B : List Gate) : Prop :=
  FanInTwo ⟨B, 0⟩ ∧ ReadsBack (h + 2) ⟨B, 0⟩ ∧ notCount ⟨B, 0⟩ = 0

lemma goodGates_nil (h : Nat) : GoodGates h [] := by
  refine ⟨(fun g hg => by cases hg), (fun j hj => by simp at hj), ?_⟩
  simp [notCount]

lemma goodGates_pos {h : Nat} {B : List Gate} (hG : GoodGates h B) : pos h ⟨B, 0⟩ :=
  ⟨⟨hG.1, hG.2.1, by simp⟩, hG.2.2⟩

lemma goodGates_snoc {h : Nat} {B : List Gate} (hG : GoodGates h B)
    {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or) {w1 w2 : Nat}
    (hw1 : w1 < h + 2 + B.length) (hw2 : w2 < h + 2 + B.length) :
    GoodGates h (B ++ [⟨op, [w1, w2]⟩]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hG.1 g hg
    · refine ⟨?_, by simp⟩
      rcases hop with rfl | rfl <;> simp
  · intro j hj u hu
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < B.length
    · have hga : gateAt ⟨B ++ [⟨op, [w1, w2]⟩], 0⟩ j = gateAt ⟨B, 0⟩ j := by
        rw [gateAt_eq (by simp; omega), gateAt_eq hlt]
        simp [List.getElem_append_left hlt]
      rw [hga] at hu
      exact hG.2.1 j hlt u hu
    · have hjeq : j = B.length := by omega
      subst hjeq
      have hga : gateAt ⟨B ++ [⟨op, [w1, w2]⟩], 0⟩ B.length = ⟨op, [w1, w2]⟩ := by
        rw [gateAt_eq (by simp)]
        simp
      rw [hga] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> assumption
  · rw [notCount_zero_iff]
    intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact (notCount_zero_iff ⟨B, 0⟩).mp hG.2.2 g hg
    · rcases hop with rfl | rfl <;> simp

lemma wires_append_getD_old {h : Nat} {B extra : List Gate} {x : List Bool}
    (hx : x.length = h + 2) {w : Nat} (hw : w < h + 2 + B.length) :
    (Circuit.wires ⟨B ++ extra, 0⟩ x).getD w false = (Circuit.wires ⟨B, 0⟩ x).getD w false := by
  rw [wires_eq_runFold, wires_eq_runFold]
  exact runFold_getD_append_left _ x B extra w false (by rw [hx]; exact hw)

lemma depths_append_getD_old {h : Nat} {B extra : List Gate} {w : Nat}
    (hw : w < h + 2 + B.length) :
    (depths h ⟨B ++ extra, 0⟩).getD w 0 = (depths h ⟨B, 0⟩).getD w 0 := by
  rw [depths_eq_runFold, depths_eq_runFold]
  exact runFold_getD_append_left _ (List.replicate (h + 2) 0) B extra w 0 (by simp; omega)

noncomputable def addBinBatch {k : Nat} (h : Nat) (op : GateOp)
    (L : List (Finset (Fin k))) (f1 f2 : Finset (Fin k) → Nat) (B : List Gate) :
    List Gate × (Finset (Fin k) → Nat) :=
  match L with
  | [] => (B, fun _ => h)
  | A :: rest =>
    let w := h + 2 + B.length
    let B1 := B ++ [⟨op, [f1 A, f2 A]⟩]
    let res := addBinBatch h op rest f1 f2 B1
    (res.1, fun X => if X = A then w else res.2 X)

lemma addBinBatch_spec {k : Nat} (h : Nat) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (L : List (Finset (Fin k))) (f1 f2 : Finset (Fin k) → Nat) (B : List Gate)
    (hG : GoodGates h B)
    (hf : ∀ A ∈ L, f1 A < h + 2 + B.length ∧ f2 A < h + 2 + B.length) :
    let res := addBinBatch h op L f1 f2 B
    (∃ extra, res.1 = B ++ extra) ∧
    res.1.length = B.length + L.length ∧
    GoodGates h res.1 ∧
    (∀ A ∈ L, res.2 A < h + 2 + res.1.length) ∧
    (∀ (x : List Bool), x.length = h + 2 → ∀ A ∈ L,
      (Circuit.wires ⟨res.1, 0⟩ x).getD (res.2 A) false =
        op.eval [(Circuit.wires ⟨B, 0⟩ x).getD (f1 A) false,
                 (Circuit.wires ⟨B, 0⟩ x).getD (f2 A) false]) ∧
    (∀ A ∈ L,
      (depths h ⟨res.1, 0⟩).getD (res.2 A) 0 ≤
        1 + max ((depths h ⟨B, 0⟩).getD (f1 A) 0) ((depths h ⟨B, 0⟩).getD (f2 A) 0)) := by
  induction L generalizing B with
  | nil =>
    exact ⟨⟨[], by simp [addBinBatch]⟩, by simp [addBinBatch], hG,
      (fun _ hA => by cases hA), (fun _ _ _ hA => by cases hA), (fun _ hA => by cases hA)⟩
  | cons A rest ih =>
    have hA := hf A (List.mem_cons_self ..)
    let B1 := B ++ [⟨op, [f1 A, f2 A]⟩]
    have hG1 : GoodGates h B1 := goodGates_snoc hG hop hA.1 hA.2
    have hf1 : ∀ X ∈ rest, f1 X < h + 2 + B1.length ∧ f2 X < h + 2 + B1.length := by
      intro X hX
      have := hf X (List.mem_cons_of_mem A hX)
      simp only [B1, List.length_append, List.length_singleton]
      omega
    obtain ⟨⟨ext, hext⟩, hlen, hG2, hlt2, hval2, hdep2⟩ := ih B1 hG1 hf1
    have hB1_len : B1.length = B.length + 1 := by simp [B1]
    have hext_full : (addBinBatch h op (A :: rest) f1 f2 B).1 =
        B ++ ([⟨op, [f1 A, f2 A]⟩] ++ ext) := by
      change (addBinBatch h op rest f1 f2 B1).1 = _
      rw [hext]; simp [B1, List.append_assoc]
    refine ⟨⟨[⟨op, [f1 A, f2 A]⟩] ++ ext, hext_full⟩, ?_, hG2, ?_, ?_, ?_⟩
    · change (addBinBatch h op rest f1 f2 B1).1.length = B.length + (rest.length + 1)
      rw [hlen, hB1_len]; omega
    · intro X hX
      change (if X = A then h + 2 + B.length else (addBinBatch h op rest f1 f2 B1).2 X) <
        h + 2 + (addBinBatch h op rest f1 f2 B1).1.length
      split_ifs with hXA
      · rw [hlen, hB1_len]; omega
      · exact hlt2 X (List.mem_of_ne_of_mem hXA hX)
    · intro x hx X hX
      change (Circuit.wires ⟨(addBinBatch h op rest f1 f2 B1).1, 0⟩ x).getD
        (if X = A then h + 2 + B.length else (addBinBatch h op rest f1 f2 B1).2 X) false = _
      split_ifs with hXA
      · subst hXA
        rw [hext, wires_append_getD_old hx (by rw [hB1_len]; omega)]
        rw [wires_getD_gate hG1.2.1 hx (t := B.length) (by simp [Circuit.size, B1])]
        have hga : gateAt ⟨B1, 0⟩ B.length = ⟨op, [f1 X, f2 X]⟩ := by
          rw [gateAt_eq (by simp [B1])]; simp [B1]
        rw [hga]
        simp only [List.map_cons, List.map_nil]
        rw [wires_append_getD_old hx hA.1, wires_append_getD_old hx hA.2]
      · have hXr := List.mem_of_ne_of_mem hXA hX
        rw [hval2 x hx X hXr]
        have hX0 := hf X hX
        rw [wires_append_getD_old hx hX0.1, wires_append_getD_old hx hX0.2]
    · intro X hX
      change (depths h ⟨(addBinBatch h op rest f1 f2 B1).1, 0⟩).getD
        (if X = A then h + 2 + B.length else (addBinBatch h op rest f1 f2 B1).2 X) 0 ≤ _
      split_ifs with hXA
      · subst hXA
        rw [hext, depths_append_getD_old (by rw [hB1_len]; omega)]
        rw [depths_getD_gate hG1.2.1 (t := B.length) (by simp [Circuit.size, B1])]
        have hga : gateAt ⟨B1, 0⟩ B.length = ⟨op, [f1 X, f2 X]⟩ := by
          rw [gateAt_eq (by simp [B1])]; simp [B1]
        rw [hga]
        simp only [List.foldl_cons, List.foldl_nil, Nat.zero_max]
        rw [depths_append_getD_old hA.1, depths_append_getD_old hA.2]
      · have hXr := List.mem_of_ne_of_mem hXA hX
        have hX0 := hf X hX
        have hd := hdep2 X hXr
        rw [depths_append_getD_old hX0.1, depths_append_getD_old hX0.2] at hd
        exact hd

noncomputable def elimVars {k : Nat} (h : Nat) :
    List (Fin k) → Finset (Fin k) → List Gate → (Finset (Fin k) → Nat) →
    List Gate × (Finset (Fin k) → Nat)
  | [], _, B, T => (B, T)
  | x :: xs, S, B, T =>
    let S' := S.erase x
    let res1 := addBinBatch h GateOp.or S'.powerset.toList T (fun A => T (insert x A)) B
    elimVars h xs S' res1.1 res1.2

lemma elimVars_spec {k : Nat} (h : Nat)
    (F : List (Fin k)) (S : Finset (Fin k)) (B : List Gate) (T : Finset (Fin k) → Nat)
    (hnd : F.Nodup) (hFS : ∀ x ∈ F, x ∈ S)
    (hG : GoodGates h B)
    (hTlt : ∀ A ⊆ S, T A < h + 2 + B.length)
    (d : Nat) (hTdep : ∀ A ⊆ S, (depths h ⟨B, 0⟩).getD (T A) 0 ≤ d) :
    let res := elimVars h F S B T
    let Sfin := S \ F.toFinset
    (∃ extra, res.1 = B ++ extra) ∧
    res.1.length + 2 ^ Sfin.card = B.length + 2 ^ S.card ∧
    GoodGates h res.1 ∧
    (∀ A ⊆ Sfin, res.2 A < h + 2 + res.1.length) ∧
    (∀ (x : List Bool), x.length = h + 2 → ∀ A ⊆ Sfin,
      (Circuit.wires ⟨res.1, 0⟩ x).getD (res.2 A) false = true ↔
        ∃ A0 ⊆ S, A0 ∩ Sfin = A ∧ (Circuit.wires ⟨B, 0⟩ x).getD (T A0) false = true) ∧
    (∀ A ⊆ Sfin, (depths h ⟨res.1, 0⟩).getD (res.2 A) 0 ≤ d + F.length) := by
  induction F generalizing S B T d with
  | nil =>
    have hSfin : S \ ([] : List (Fin k)).toFinset = S := by simp
    refine ⟨⟨[], by simp [elimVars]⟩, by simp [elimVars], hG,
      fun A hA => hTlt A (hSfin ▸ hA), ?_, fun A hA => by simpa [elimVars] using hTdep A (hSfin ▸ hA)⟩
    intro x _ A hA
    rw [hSfin] at hA ⊢
    constructor
    · intro hv
      exact ⟨A, hA, Finset.inter_eq_left.mpr hA, hv⟩
    · rintro ⟨A0, hA0, hEq, hv⟩
      have hA0eq : A0 = A := by rw [← hEq, Finset.inter_eq_left.mpr hA0]
      rwa [← hA0eq]
  | cons a xs ih =>
    rw [List.nodup_cons] at hnd
    have haS : a ∈ S := hFS a (List.mem_cons_self ..)
    set S' := S.erase a
    set L := S'.powerset.toList
    have hLmem : ∀ A, A ∈ L ↔ A ⊆ S' := by
      intro A; simp [L, Finset.mem_powerset]
    have hLlen : L.length = 2 ^ S'.card := by
      simp [L, Finset.length_toList, Finset.card_powerset]
    have hCardS : S.card = S'.card + 1 := (Finset.card_erase_add_one haS).symm
    have hf : ∀ A ∈ L, T A < h + 2 + B.length ∧ T (insert a A) < h + 2 + B.length := by
      intro A hA
      have hAS' : A ⊆ S' := (hLmem A).mp hA
      refine ⟨hTlt A (hAS'.trans (Finset.erase_subset a S)), hTlt (insert a A) ?_⟩
      exact Finset.insert_subset haS (hAS'.trans (Finset.erase_subset a S))
    set res1 := addBinBatch h GateOp.or L T (fun A => T (insert a A)) B
    obtain ⟨⟨ext1, hext1⟩, hlen1, hG1, hlt1, hval1, hdep1⟩ :=
      addBinBatch_spec h GateOp.or (Or.inr rfl) L T (fun A => T (insert a A)) B hG hf
    have hxsS' : ∀ z ∈ xs, z ∈ S' := by
      intro z hz
      exact Finset.mem_erase.mpr ⟨fun hza => hnd.1 (hza ▸ hz), hFS z (List.mem_cons_of_mem a hz)⟩
    have hT1lt : ∀ A ⊆ S', res1.2 A < h + 2 + res1.1.length :=
      fun A hA => hlt1 A ((hLmem A).mpr hA)
    have hT1dep : ∀ A ⊆ S', (depths h ⟨res1.1, 0⟩).getD (res1.2 A) 0 ≤ d + 1 := by
      intro A hA
      have h1 : (depths h ⟨res1.1, 0⟩).getD (res1.2 A) 0 ≤ 1 + max ((depths h ⟨B, 0⟩).getD (T A) 0) ((depths h ⟨B, 0⟩).getD (T (insert a A)) 0) := hdep1 A ((hLmem A).mpr hA)
      have hAS : A ⊆ S := hA.trans (Finset.erase_subset a S)
      have hAiS : insert a A ⊆ S := Finset.insert_subset haS hAS
      have hd1 := hTdep A hAS
      have hd2 := hTdep (insert a A) hAiS
      omega
    obtain ⟨⟨ext2, hext2⟩, hlen2, hG2, hlt2, hval2, hdep2⟩ :=
      ih S' res1.1 res1.2 hnd.2 hxsS' hG1 hT1lt (d + 1) hT1dep
    have hSfinEq : S' \ xs.toFinset = S \ (a :: xs).toFinset := by
      ext z
      simp only [S', Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons, Finset.mem_insert,
        not_or]
      tauto
    refine ⟨⟨ext1 ++ ext2, ?_⟩, ?_, hG2, ?_, ?_, ?_⟩
    · change (elimVars h xs S' res1.1 res1.2).1 = B ++ (ext1 ++ ext2)
      rw [hext2, hext1, List.append_assoc]
    · change (elimVars h xs S' res1.1 res1.2).1.length + 2 ^ (S \ (a :: xs).toFinset).card = _
      rw [← hSfinEq, hlen2, hlen1, hLlen, hCardS, pow_succ]
      omega
    · intro A hA
      rw [← hSfinEq] at hA
      exact hlt2 A hA
    · intro x hx A hA
      rw [← hSfinEq] at hA
      have hiff := hval2 x hx A hA
      change (Circuit.wires ⟨(elimVars h xs S' res1.1 res1.2).1, 0⟩ x).getD
        ((elimVars h xs S' res1.1 res1.2).2 A) false = true ↔ _
      rw [hiff]
      constructor
      · rintro ⟨A1, hA1S', hA1eq, hA1v⟩
        have hv1 := hval1 x hx A1 ((hLmem A1).mpr hA1S')
        rw [hv1] at hA1v
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true] at hA1v
        rcases hA1v with hvA1 | hvA1a
        · refine ⟨A1, hA1S'.trans (Finset.erase_subset a S), ?_, hvA1⟩
          rw [← hSfinEq]; exact hA1eq
        · refine ⟨insert a A1, Finset.insert_subset haS (hA1S'.trans (Finset.erase_subset a S)), ?_, hvA1a⟩
          rw [← hSfinEq]
          have haNot : a ∉ S' \ xs.toFinset := by simp [S']
          ext z
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hz1, hz2⟩
            · exact absurd hz2 haNot
            · rw [← hA1eq]; exact Finset.mem_inter.mpr ⟨hz1, hz2⟩
          · intro hz
            rw [← hA1eq] at hz
            exact ⟨Or.inr (Finset.mem_inter.mp hz).1, (Finset.mem_inter.mp hz).2⟩
      · rintro ⟨A0, hA0S, hA0eq, hA0v⟩
        rw [← hSfinEq] at hA0eq
        let A1 := A0.erase a
        have hA1S' : A1 ⊆ S' := Finset.erase_subset_erase a hA0S
        have hA1eq : A1 ∩ (S' \ xs.toFinset) = A := by
          rw [← hA0eq]
          ext z
          simp only [A1, Finset.mem_inter, Finset.mem_erase, Finset.mem_sdiff, S']
          tauto
        refine ⟨A1, hA1S', hA1eq, ?_⟩
        rw [hval1 x hx A1 ((hLmem A1).mpr hA1S')]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
        by_cases ha0 : a ∈ A0
        · right
          have hins : insert a A1 = A0 := Finset.insert_erase ha0
          rwa [hins]
        · left
          have her : A1 = A0 := Finset.erase_eq_of_notMem ha0
          rwa [her]
    · intro A hA
      rw [← hSfinEq] at hA
      have hd : (depths h ⟨(elimVars h (a :: xs) S B T).1, 0⟩).getD ((elimVars h (a :: xs) S B T).2 A) 0 ≤ d + 1 + xs.length := hdep2 A hA
      simp only [List.length_cons]
      omega

structure CompState (k : Nat) where
  gates : List Gate
  tab : Nat → Finset (Fin k) → Nat
  finW : Nat → Nat

noncomputable def litWire {h k : Nat} (e : Fin h → Fin k)
    (j : Fin k) : Nat :=
  if hj : ∃ a : Fin h, e a = j then (Classical.choose hj).val else h + 1

noncomputable def onesOf {h k : Nat} (e : Fin h → Fin k)
    (Y : Finset (Fin h)) : Finset (Fin k) :=
  (Finset.univ \ Finset.univ.image e) ∪ Y.image e

lemma litWire_lt {h k : Nat} (e : Fin h → Fin k) (j : Fin k) :
    litWire e j < h + 2 := by
  unfold litWire
  split_ifs with hj
  · have := (Classical.choose hj).isLt; omega
  · omega

lemma litWire_val {h k : Nat} {e : Fin h → Fin k}
    (he : Function.Injective e) (Y : Finset (Fin h)) (j : Fin k) :
    (visInput Y).getD (litWire e j) false = @decide (j ∈ onesOf e Y) (Classical.propDecidable _) := by
  unfold litWire onesOf
  split_ifs with hj
  · let a := Classical.choose hj
    have ha : e a = j := Classical.choose_spec hj
    rw [visInput_getD_var Y a]
    congr 1
    apply propext
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_image, true_and]
    constructor
    · intro haY
      exact Or.inr ⟨a, haY, ha⟩
    · rintro (hpriv | ⟨b, hbY, hbe⟩)
      · exact absurd ⟨a, ha⟩ hpriv
      · have hab : b = a := he (hbe.trans ha.symm)
        rwa [← hab]
  · rw [visInput_getD_const1 Y]
    symm
    rw [@decide_eq_true_eq _ (Classical.propDecidable _)]
    refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, ?_⟩)
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact hj

noncomputable def initComp {h k : Nat} (e : Fin h → Fin k)
    (held : Nat → Finset (Fin k)) : CompState k :=
  { gates := []
    tab := fun w A =>
      if h1 : w < k then
        let j : Fin k := ⟨w, h1⟩
        if j ∈ held w ∧ j ∉ A then h else litWire e j
      else if h2 : w < 2 * k then
        let j : Fin k := ⟨w - k, by omega⟩
        if j ∈ A then h else h + 1
      else if w = 2 * k then h
      else h + 1
    finW := fun w =>
      if h1 : w < k then litWire e ⟨w, h1⟩
      else if w < 2 * k then h + 1
      else if w = 2 * k then h
      else h + 1 }

def varsAt (k : Nat) (D : Circuit) (w : Nat) : Finset (Fin k) :=
  let s := (wireInfo k D).getD w (∅, ∅)
  s.1 ∪ s.2

noncomputable def compileOneGate {k : Nat}
    (h : Nat) (D : Circuit) (held : Nat → Finset (Fin k))
    (t : Nat) (st : CompState k) : CompState k :=
  let src := 2 * k + 2
  let j := src + t
  let g := gateAt D t
  let Bt := held j ∪ crossGate k D t
  match g.inputs with
  | [] =>
    let w := if g.op = GateOp.and then h + 1 else h
    { gates := st.gates
      tab := fun w0 A => if w0 = j then w else st.tab w0 A
      finW := fun w0 => if w0 = j then w else st.finW w0 }
  | [u] =>
    let Su := Bt ∩ varsAt k D u
    let resU := elimVars h (held u \ Su).toList (held u) st.gates (st.tab u)
    let Tj := fun A => resU.2 (A ∩ Su)
    let resF := elimVars h (held j).toList (held j) resU.1 Tj
    { gates := resF.1
      tab := fun w0 A => if w0 = j then Tj A else st.tab w0 A
      finW := fun w0 => if w0 = j then resF.2 ∅ else st.finW w0 }
  | u :: v :: _ =>
    let Su := Bt ∩ varsAt k D u
    let Sv := Bt ∩ varsAt k D v
    let resU := elimVars h (held u \ Su).toList (held u) st.gates (st.tab u)
    let resV := elimVars h (held v \ Sv).toList (held v) resU.1 (st.tab v)
    let resM := addBinBatch h g.op Bt.powerset.toList
      (fun C => resU.2 (C ∩ Su)) (fun C => resV.2 (C ∩ Sv)) resV.1
    let resJ := elimVars h (Bt \ held j).toList Bt resM.1 resM.2
    let resF := elimVars h (held j).toList (held j) resJ.1 resJ.2
    { gates := resF.1
      tab := fun w0 A => if w0 = j then resJ.2 A else st.tab w0 A
      finW := fun w0 => if w0 = j then resF.2 ∅ else st.finW w0 }

noncomputable def compileUpTo {h k : Nat}
    (e : Fin h → Fin k) (D : Circuit) (held : Nat → Finset (Fin k)) :
    Nat → CompState k
  | 0 => initComp e held
  | m + 1 => compileOneGate h D held m (compileUpTo e D held m)

def CertAt {h k : Nat} (e : Fin h → Fin k) (D : Circuit)
    (held : Nat → Finset (Fin k)) (Y : Finset (Fin h)) (w : Nat) (A : Finset (Fin k)) : Prop :=
  ∃ P N : Finset (Fin k),
    P ⊆ ((wireInfo k D).getD w (∅, ∅)).1 ∧
    N ⊆ ((wireInfo k D).getD w (∅, ∅)).2 ∧
    P ⊆ onesOf e Y ∧
    Disjoint P N ∧
    Disjoint P (held w \ A) ∧
    Disjoint N A ∧
    ∀ X : Finset (Fin k), P ⊆ X → Disjoint N X →
      (D.wires (word X (Finset.univ \ X))).getD w false = true

lemma cert_on_sub {h k : Nat} {e : Fin h → Fin k} {D : Circuit}
    {held : Nat → Finset (Fin k)} {Y : Finset (Fin h)} {u : Nat} {S A0 A : Finset (Fin k)}
    (hS : S ⊆ held u) (hEq : A0 ∩ S = A) (hC : CertAt e D held Y u A0) :
    ∃ P N : Finset (Fin k),
      P ⊆ ((wireInfo k D).getD u (∅, ∅)).1 ∧
      N ⊆ ((wireInfo k D).getD u (∅, ∅)).2 ∧
      P ⊆ onesOf e Y ∧
      Disjoint P N ∧
      Disjoint P (S \ A) ∧
      Disjoint N A ∧
      ∀ X : Finset (Fin k), P ⊆ X → Disjoint N X →
        (D.wires (word X (Finset.univ \ X))).getD u false = true := by
  obtain ⟨P, N, hP, hN, hPo, hdPN, hdP, hdN, hX⟩ := hC
  refine ⟨P, N, hP, hN, hPo, hdPN, ?_, ?_, hX⟩
  · rw [Finset.disjoint_left]
    intro x hxP hxSA
    have hxS := (Finset.mem_sdiff.mp hxSA).1
    have hxA := (Finset.mem_sdiff.mp hxSA).2
    have hxA0 : x ∉ A0 := fun h0 => hxA (hEq ▸ Finset.mem_inter.mpr ⟨h0, hxS⟩)
    exact Finset.disjoint_left.mp hdP hxP (Finset.mem_sdiff.mpr ⟨hS hxS, hxA0⟩)
  · rw [Finset.disjoint_left]
    intro x hxN hxA
    rw [← hEq] at hxA
    exact Finset.disjoint_left.mp hdN hxN (Finset.mem_inter.mp hxA).1

lemma lift_disjoint_vars {k : Nat} {P N B S A V : Finset (Fin k)}
    (hPV : P ⊆ V) (hNV : N ⊆ V) (hS : S = B ∩ V) (hAB : A ⊆ B)
    (hP : Disjoint P (S \ (A ∩ S))) (hN : Disjoint N (A ∩ S)) :
    Disjoint P (B \ A) ∧ Disjoint N A := by
  constructor
  · rw [Finset.disjoint_left]
    intro x hxP hxBA
    have hxS : x ∈ S := by
      rw [hS]; exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hxBA).1, hPV hxP⟩
    have hxnA : x ∉ A ∩ S := fun h => (Finset.mem_sdiff.mp hxBA).2 (Finset.mem_inter.mp h).1
    exact Finset.disjoint_left.mp hP hxP (Finset.mem_sdiff.mpr ⟨hxS, hxnA⟩)
  · rw [Finset.disjoint_left]
    intro x hxN hxA
    have hxS : x ∈ S := by rw [hS]; exact Finset.mem_inter.mpr ⟨hAB hxA, hNV hxN⟩
    exact Finset.disjoint_left.mp hN hxN (Finset.mem_inter.mpr ⟨hxA, hxS⟩)

lemma sdiff_toList_eq {k : Nat} (S T : Finset (Fin k)) (hT : T ⊆ S) :
    S \ (S \ T).toList.toFinset = T := by
  ext x
  simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_toList]
  constructor
  · intro ⟨hxS, hnot⟩
    by_contra hxT
    exact hnot ⟨hxS, hxT⟩
  · intro hxT
    exact ⟨hT hxT, fun h => h.2 hxT⟩

lemma sdiff_self_toList_eq {k : Nat} (S : Finset (Fin k)) :
    S \ S.toList.toFinset = ∅ := by
  ext x
  simp

def CompInv {h k : Nat} (e : Fin h → Fin k) (D : Circuit)
    (held : Nat → Finset (Fin k)) (width m : Nat) (st : CompState k) : Prop :=
  let src := 2 * k + 2
  GoodGates h st.gates ∧
  st.gates.length ≤ 5 * 2 ^ width * m ∧
  (∀ w < src + m, ∀ A ⊆ held w, st.tab w A < h + 2 + st.gates.length) ∧
  (∀ w < src + m, st.finW w < h + 2 + st.gates.length) ∧
  (∀ w < src + m, ∀ A ⊆ held w,
    (depths h ⟨st.gates, 0⟩).getD (st.tab w A) 0 ≤
      (2 * width + 1) * (depths (2 * k) D).getD w 0) ∧
  (∀ w < src + m,
    (depths h ⟨st.gates, 0⟩).getD (st.finW w) 0 ≤
      (2 * width + 1) * (depths (2 * k) D).getD w 0 + 2 * width) ∧
  (∀ (Y : Finset (Fin h)) (w : Nat), w < src + m → ∀ A ⊆ held w,
    (Circuit.wires ⟨st.gates, 0⟩ (visInput Y)).getD (st.tab w A) false = true →
      CertAt e D held Y w A) ∧
  (∀ (Y : Finset (Fin h)) (w : Nat), w < src + m →
    (Circuit.wires ⟨st.gates, 0⟩ (visInput Y)).getD (st.finW w) false = true →
      ∃ A ⊆ held w, CertAt e D held Y w A) ∧
  (∀ (Y : Finset (Fin h)) (X : Finset (Fin k)), X ⊆ onesOf e Y → ∀ w < src + m,
    (D.wires (word X (Finset.univ \ X))).getD w false = true →
      (Circuit.wires ⟨st.gates, 0⟩ (visInput Y)).getD (st.tab w (X ∩ held w)) false = true ∧
      (Circuit.wires ⟨st.gates, 0⟩ (visInput Y)).getD (st.finW w) false = true)

lemma initComp_inv {h k : Nat} {e : Fin h → Fin k}
    (he : Function.Injective e) {D : Circuit} (held : Nat → Finset (Fin k)) (width : Nat) :
    CompInv e D held width 0 (initComp e held) := by
  refine ⟨goodGates_nil h, by simp [initComp], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w _ A _
    unfold initComp
    dsimp only
    split_ifs <;> first | exact litWire_lt e _ | omega
  · intro w _
    unfold initComp
    dsimp only
    split_ifs <;> first | exact litWire_lt e _ | omega
  · intro w _ A _
    have hlt : (initComp e held).tab w A < h + 2 := by
      unfold initComp; dsimp only
      split_ifs <;> first | exact litWire_lt e _ | omega
    rw [depths_getD_input h _ _ hlt]; omega
  · intro w _
    have hlt : (initComp e held).finW w < h + 2 := by
      unfold initComp; dsimp only
      split_ifs <;> first | exact litWire_lt e _ | omega
    rw [depths_getD_input h _ _ hlt]; omega
  · intro Y w hw A hA hval
    have hlt : (initComp e held).tab w A < h + 2 := by
      unfold initComp; dsimp only
      split_ifs <;> first | exact litWire_lt e _ | omega
    rw [wires_getD_input _ _ _ (by rw [visInput_length]; exact hlt)] at hval
    unfold initComp at hval
    dsimp only at hval
    split_ifs at hval with h1 h1a h2 h2a h3
    · rw [visInput_getD_const0] at hval; cases hval
    · let j : Fin k := ⟨w, h1⟩
      rw [litWire_val he Y j] at hval
      have hj : j ∈ onesOf e Y := by simpa using hval
      refine ⟨{j}, ∅, ?_, by simp, by simpa using hj, by simp, ?_, by simp, ?_⟩
      · rw [wireInfo_getD_pos k D j]
      · rw [Finset.disjoint_left]
        intro x hx hxS
        have hxje : x = j := Finset.mem_singleton.mp hx
        subst hxje
        have hm := Finset.mem_sdiff.mp hxS
        exact h1a ⟨hm.1, hm.2⟩
      · intro X hPX _
        have hjX : j ∈ X := hPX (Finset.mem_singleton_self j)
        rw [wires_getD_input D _ w (by rw [word_length]; omega)]
        change (word X (Finset.univ \ X)).getD j.val false = true
        rw [word_getD_pos X (Finset.univ \ X) j, @decide_eq_true_eq _ (Classical.propDecidable _)]
        exact hjX
    · rw [visInput_getD_const0] at hval; cases hval
    · let j : Fin k := ⟨w - k, by omega⟩
      have hwj : w = k + j.val := by simp [j]; omega
      refine ⟨∅, {j}, by simp, ?_, by simp, by simp, by simp, ?_, ?_⟩
      · rw [hwj, wireInfo_getD_neg k D j]
      · rw [Finset.disjoint_left]
        intro x hx hxA
        have hxje : x = j := Finset.mem_singleton.mp hx
        subst hxje
        exact h2a hxA
      · intro X _ hNX
        have hjX : j ∉ X := Finset.disjoint_left.mp hNX (Finset.mem_singleton_self j)
        rw [hwj, wires_getD_input D _ (k + j.val) (by rw [word_length]; omega),
          word_getD_neg X (Finset.univ \ X) j]
        simp [hjX]
    · rw [visInput_getD_const0] at hval; cases hval
    · have hw4 : w = 2 * k + 1 := by omega
      subst hw4
      refine ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
      intro X _ _
      rw [wires_getD_input D _ (2 * k + 1) (by rw [word_length]; omega), word_getD_const1]
  · intro Y w hw hval
    have hlt : (initComp e held).finW w < h + 2 := by
      unfold initComp; dsimp only
      split_ifs <;> first | exact litWire_lt e _ | omega
    rw [wires_getD_input _ _ _ (by rw [visInput_length]; exact hlt)] at hval
    unfold initComp at hval
    dsimp only at hval
    split_ifs at hval with h1 h2 h3
    · let j : Fin k := ⟨w, h1⟩
      rw [litWire_val he Y j] at hval
      have hj : j ∈ onesOf e Y := by simpa using hval
      refine ⟨held w, Finset.Subset.refl _, {j}, ∅, ?_, by simp, by simpa using hj,
        by simp, by simp, by simp, ?_⟩
      · rw [wireInfo_getD_pos k D j]
      · intro X hPX _
        have hjX : j ∈ X := hPX (Finset.mem_singleton_self j)
        rw [wires_getD_input D _ w (by rw [word_length]; omega)]
        change (word X (Finset.univ \ X)).getD j.val false = true
        rw [word_getD_pos X (Finset.univ \ X) j, @decide_eq_true_eq _ (Classical.propDecidable _)]
        exact hjX
    · let j : Fin k := ⟨w - k, by omega⟩
      have hwj : w = k + j.val := by simp [j]; omega
      refine ⟨∅, Finset.empty_subset _, ∅, {j}, by simp, ?_, by simp, by simp, by simp, by simp, ?_⟩
      · rw [hwj, wireInfo_getD_neg k D j]
      · intro X _ hNX
        have hjX : j ∉ X := Finset.disjoint_left.mp hNX (Finset.mem_singleton_self j)
        rw [hwj, wires_getD_input D _ (k + j.val) (by rw [word_length]; omega),
          word_getD_neg X (Finset.univ \ X) j]
        simp [hjX]
    · rw [visInput_getD_const0] at hval; cases hval
    · have hw4 : w = 2 * k + 1 := by omega
      subst hw4
      refine ⟨∅, Finset.empty_subset _, ∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
      intro X _ _
      rw [wires_getD_input D _ (2 * k + 1) (by rw [word_length]; omega), word_getD_const1]
  · intro Y X hXo w hw hval
    have hltT : (initComp e held).tab w (X ∩ held w) < h + 2 := by
      unfold initComp; dsimp only
      split_ifs <;> first | exact litWire_lt e _ | omega
    have hltF : (initComp e held).finW w < h + 2 := by
      unfold initComp; dsimp only
      split_ifs <;> first | exact litWire_lt e _ | omega
    rw [wires_getD_input _ _ _ (by rw [visInput_length]; exact hltT),
      wires_getD_input _ _ _ (by rw [visInput_length]; exact hltF)]
    rw [wires_getD_input D _ w (by rw [word_length]; omega)] at hval
    unfold initComp
    dsimp only
    by_cases h1 : w < k
    · let j : Fin k := ⟨w, h1⟩
      change (word X (Finset.univ \ X)).getD j.val false = true at hval
      rw [word_getD_pos X (Finset.univ \ X) j, @decide_eq_true_eq _ (Classical.propDecidable _)] at hval
      have hjX : j ∈ X := hval
      have hjo : j ∈ onesOf e Y := hXo hjX
      have hnot : ¬ (j ∈ held w ∧ j ∉ X ∩ held w) := by
        intro ⟨hjh, hnot⟩
        exact hnot (Finset.mem_inter.mpr ⟨hjX, hjh⟩)
      simp only [h1, ↓reduceDIte]
      change (visInput Y).getD (if j ∈ held w ∧ j ∉ X ∩ held w then h else litWire e j) false = true ∧
        (visInput Y).getD (litWire e j) false = true
      rw [ite_eq_right hnot, litWire_val he Y j, @decide_eq_true_eq _ (Classical.propDecidable _)]
      exact ⟨hjo, hjo⟩
    · by_cases h2 : w < 2 * k
      · let j : Fin k := ⟨w - k, by omega⟩
        have hwj : w = k + j.val := by simp [j]; omega
        rw [hwj, word_getD_neg X (Finset.univ \ X) j, @decide_eq_true_eq _ (Classical.propDecidable _)] at hval
        have hjX : j ∉ X := (Finset.mem_sdiff.mp hval).2
        have hjn : j ∉ X ∩ held w := fun h => hjX (Finset.mem_inter.mp h).1
        simp only [h1, h2, ↓reduceDIte]
        change (visInput Y).getD (if j ∈ X ∩ held w then h else h + 1) false = true ∧
          (visInput Y).getD (h + 1) false = true
        rw [ite_eq_right hjn, visInput_getD_const1]
        exact ⟨rfl, rfl⟩
      · by_cases h3 : w = 2 * k
        · subst h3; rw [word_getD_const0] at hval; cases hval
        · simp only [h1, h2, h3, ↓reduceDIte, ↓reduceIte, visInput_getD_const1, and_self]

lemma compileOneGate_inv {h k : Nat} {e : Fin h → Fin k}
    {D : Circuit} (hpos : pos (2 * k) D) {held : Nat → Finset (Fin k)} {width : Nat}
    (hleg : (∀ j < 2 * k + 2 + D.size, held j ⊆ varsAt k D j) ∧
      ∀ t < D.size, ∀ u ∈ (gateAt D t).inputs,
        (held (2 * k + 2 + t) ∪ crossGate k D t) ∩ varsAt k D u ⊆ held u)
    (hbnd : (∀ j < 2 * k + 2, (held j).card ≤ width) ∧
      ∀ t < D.size, (held (2 * k + 2 + t) ∪ crossGate k D t).card ≤ width)
    {m : Nat} (hm : m < D.size) {st : CompState k} (hinv : CompInv e D held width m st) :
    CompInv e D held width (m + 1) (compileOneGate h D held m st) := by
  have hheld_card : ∀ w < 2 * k + 2 + D.size, (held w).card ≤ width := by
    intro w hw
    by_cases hlt : w < 2 * k + 2
    · exact hbnd.1 w hlt
    · obtain ⟨s, rfl⟩ : ∃ s, w = 2 * k + 2 + s := ⟨w - (2 * k + 2), by omega⟩
      exact (Finset.card_le_card Finset.subset_union_left).trans (hbnd.2 s (by omega))
  obtain ⟨hG, hlen, htab_lt, hfin_lt, htab_dep, hfin_dep, htab_snd, hfin_snd, hcomp⟩ := hinv
  let src := 2 * k + 2
  let j := src + m
  let g := gateAt D m
  let Bt := held j ∪ crossGate k D m
  have hBt_card : Bt.card ≤ width := hbnd.2 m hm
  have hhj_card : (held j).card ≤ width := hheld_card j (by omega)
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := pos_op hpos (gateAt_mem hm)
  have hg_len := pos_len hpos (gateAt_mem hm)
  have hpow_le : ∀ S : Finset (Fin k), S.card ≤ width → 2 ^ S.card ≤ 2 ^ width :=
    fun S hS => Nat.pow_le_pow_right (by omega) hS
  rcases list_len_le_two_cases g.inputs hg_len with hin | ⟨u, hin⟩ | ⟨u, v, hin⟩
  ·
    have hcomp_eq : compileOneGate h D held m st =
        { gates := st.gates
          tab := fun w0 A => if w0 = j then (if g.op = GateOp.and then h + 1 else h) else st.tab w0 A
          finW := fun w0 => if w0 = j then (if g.op = GateOp.and then h + 1 else h) else st.finW w0 } := by
      unfold compileOneGate; simp [g, j, src, hin]
    rw [hcomp_eq]
    refine ⟨hG, hlen.trans (Nat.mul_le_mul_left _ (by omega)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw A hA
      dsimp only; by_cases hwj : w = j
      · rw [ite_eq_left hwj]; split_ifs <;> omega
      · rw [ite_eq_right hwj]; exact htab_lt w (by dsimp [j, src] at hwj; omega) A hA
    · intro w hw
      dsimp only; by_cases hwj : w = j
      · rw [ite_eq_left hwj]; split_ifs <;> omega
      · rw [ite_eq_right hwj]; exact hfin_lt w (by dsimp [j, src] at hwj; omega)
    · intro w hw A hA
      dsimp only; by_cases hwj : w = j
      · rw [ite_eq_left hwj]
        have hlt : (if g.op = GateOp.and then h + 1 else h) < h + 2 := by split_ifs <;> omega
        rw [depths_getD_input h _ _ hlt]; omega
      · rw [ite_eq_right hwj]; exact htab_dep w (by dsimp [j, src] at hwj; omega) A hA
    · intro w hw
      dsimp only; by_cases hwj : w = j
      · rw [ite_eq_left hwj]
        have hlt : (if g.op = GateOp.and then h + 1 else h) < h + 2 := by split_ifs <;> omega
        rw [depths_getD_input h _ _ hlt]; omega
      · rw [ite_eq_right hwj]; exact hfin_dep w (by dsimp [j, src] at hwj; omega)
    · intro Y w hw A hA hv
      dsimp only at hv; by_cases hwj : w = j
      · subst hwj; rw [ite_eq_left rfl] at hv
        have hlt : (if g.op = GateOp.and then h + 1 else h) < h + 2 := by split_ifs <;> omega
        rw [wires_getD_input _ _ _ (by rw [visInput_length]; exact hlt)] at hv
        split_ifs at hv with hand
        · refine ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
          intro X _ _
          rw [wires_getD_gate hpos.1.2.1 (word_length X _) hm]
          change g.op.eval (g.inputs.map _) = true
          rw [hand, hin]; rfl
        · rw [visInput_getD_const0] at hv; cases hv
      · rw [ite_eq_right hwj] at hv; exact htab_snd Y w (by dsimp [j, src] at hwj; omega) A hA hv
    · intro Y w hw hv
      dsimp only at hv; by_cases hwj : w = j
      · subst hwj; rw [ite_eq_left rfl] at hv
        have hlt : (if g.op = GateOp.and then h + 1 else h) < h + 2 := by split_ifs <;> omega
        rw [wires_getD_input _ _ _ (by rw [visInput_length]; exact hlt)] at hv
        split_ifs at hv with hand
        · refine ⟨∅, Finset.empty_subset _, ∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
          intro X _ _
          rw [wires_getD_gate hpos.1.2.1 (word_length X _) hm]
          change g.op.eval (g.inputs.map _) = true
          rw [hand, hin]; rfl
        · rw [visInput_getD_const0] at hv; cases hv
      · rw [ite_eq_right hwj] at hv; exact hfin_snd Y w (by dsimp [j, src] at hwj; omega) hv
    · intro Y X hXo w hw hv
      dsimp only; by_cases hwj : w = j
      · subst hwj; rw [ite_eq_left rfl, ite_eq_left rfl]
        rw [wires_getD_gate hpos.1.2.1 (word_length X _) hm] at hv
        change g.op.eval (g.inputs.map _) = true at hv
        rcases hop with hand | hor
        · have hlt : (if g.op = GateOp.and then h + 1 else h) < h + 2 := by simp [hand]
          rw [wires_getD_input _ _ _ (by rw [visInput_length]; exact hlt)]
          rw [ite_eq_left hand, visInput_getD_const1]
          exact ⟨rfl, rfl⟩
        · rw [hor, hin] at hv; cases hv
      · rw [ite_eq_right hwj, ite_eq_right hwj]; exact hcomp Y X hXo w (by dsimp [j, src] at hwj; omega) hv
  ·
    have hu_mem : u ∈ g.inputs := by rw [hin]; simp
    have hu_lt : u < src + m := hpos.1.2.1 m hm u hu_mem
    have hu_card : (held u).card ≤ width := hheld_card u (by omega)
    have hcr : crossGate k D m = ∅ := by
      unfold crossGate
      dsimp only
      change (if g.op = GateOp.and then (((g.inputs.head?.map (fun j => (wireInfo k D).getD j (∅, ∅))).getD (∅, ∅)).1 ∩
        ((g.inputs[1]?.map (fun j => (wireInfo k D).getD j (∅, ∅))).getD (∅, ∅)).2) ∪
        (((g.inputs.head?.map (fun j => (wireInfo k D).getD j (∅, ∅))).getD (∅, ∅)).2 ∩
        ((g.inputs[1]?.map (fun j => (wireInfo k D).getD j (∅, ∅))).getD (∅, ∅)).1) else ∅) = ∅
      rw [hin]
      simp
    have hBt_eq : Bt = held j := by simp [Bt, hcr]
    let Su := Bt ∩ varsAt k D u
    have hSu_sub : Su ⊆ held u := hleg.2 m hm u hu_mem
    have hSu_eq : held u \ (held u \ Su).toList.toFinset = Su := sdiff_toList_eq (held u) Su hSu_sub
    let du := (2 * width + 1) * (depths (2 * k) D).getD u 0
    let resU := elimVars h (held u \ Su).toList (held u) st.gates (st.tab u)
    obtain ⟨⟨extU, hextU⟩, hlenU, hGU, hltU, hvalU, hdepU⟩ :=
      elimVars_spec h (held u \ Su).toList (held u) st.gates (st.tab u)
        (Finset.nodup_toList _) (fun x hx => (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1)
        hG (fun A hA => htab_lt u hu_lt A hA) du (fun A hA => htab_dep u hu_lt A hA)
    have hresU_len : resU.1.length ≤ st.gates.length + 2 ^ width :=
      (Nat.le_add_right _ _).trans (hlenU.le.trans (Nat.add_le_add_left (hpow_le (held u) hu_card) _))
    let Tj := fun A => resU.2 (A ∩ Su)
    have hTj_lt : ∀ A ⊆ held j, Tj A < h + 2 + resU.1.length := by
      intro A _
      exact hltU (A ∩ Su) (hSu_eq.symm ▸ Finset.inter_subset_right)
    have hdep_j : (depths (2 * k) D).getD j 0 = 1 + (depths (2 * k) D).getD u 0 := by
      rw [depths_getD_gate hpos.1.2.1 hm]
      change 1 + g.inputs.foldl _ 0 = _
      simp [hin]
    have hFu_len : (held u \ Su).toList.length ≤ width := by
      rw [Finset.length_toList]
      exact (Finset.card_le_card Finset.sdiff_subset).trans hu_card
    have hTj_dep : ∀ A ⊆ held j, (depths h ⟨resU.1, 0⟩).getD (Tj A) 0 ≤ du + width := by
      intro A _
      have hd : (depths h ⟨resU.1, 0⟩).getD (Tj A) 0 ≤ du + (held u \ Su).toList.length := hdepU (A ∩ Su) (hSu_eq.symm ▸ Finset.inter_subset_right)
      omega
    let resF := elimVars h (held j).toList (held j) resU.1 Tj
    obtain ⟨⟨extF, hextF⟩, hlenF, hGF, hltF, hvalF, hdepF⟩ :=
      elimVars_spec h (held j).toList (held j) resU.1 Tj
        (Finset.nodup_toList _) (fun x hx => Finset.mem_toList.mp hx)
        hGU hTj_lt (du + width) hTj_dep
    have hresF_len : resF.1.length ≤ resU.1.length + 2 ^ width :=
      (Nat.le_add_right _ _).trans (hlenF.le.trans (Nat.add_le_add_left (hpow_le (held j) hhj_card) _))
    have hext_all : resF.1 = st.gates ++ (extU ++ extF) := by
      rw [hextF, hextU, List.append_assoc]
    have hcomp_eq : compileOneGate h D held m st =
        { gates := resF.1
          tab := fun w0 A => if w0 = j then Tj A else st.tab w0 A
          finW := fun w0 => if w0 = j then resF.2 ∅ else st.finW w0 } := by
      unfold compileOneGate; simp [g, j, src, hin, Bt, Su, resU, Tj, resF]
    rw [hcomp_eq]
    have hFj_len : (held j).toList.length ≤ width := by
      rw [Finset.length_toList]; exact hhj_card
    have hmu := wireInfo_mono hpos.1.2.1 hm hu_mem
    refine ⟨hGF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change resF.1.length ≤ 5 * 2 ^ width * (m + 1)
      have : 5 * 2 ^ width * (m + 1) = 5 * 2 ^ width * m + 5 * 2 ^ width := by ring
      omega
    · intro w hw A hA
      dsimp only; split_ifs with hwj
      · subst hwj
        have h1 := hTj_lt A hA
        rw [hextF, List.length_append]; omega
      · have h1 := htab_lt w (by omega) A hA
        rw [hext_all, List.length_append]; omega
    · intro w hw
      dsimp only; split_ifs with hwj
      · subst hwj
        exact hltF ∅ (Finset.empty_subset _)
      · have h1 := hfin_lt w (by omega)
        rw [hext_all, List.length_append]; omega
    · intro w hw A hA
      dsimp only; split_ifs with hwj
      · subst hwj
        rw [hextF, depths_append_getD_old (hTj_lt A hA)]
        have h1 := hTj_dep A hA
        rw [hdep_j]
        have : (2 * width + 1) * (1 + (depths (2 * k) D).getD u 0) =
            du + (2 * width + 1) := by dsimp [du]; ring
        omega
      · rw [hext_all, depths_append_getD_old (htab_lt w (by omega) A hA)]
        exact htab_dep w (by omega) A hA
    · intro w hw
      dsimp only; split_ifs with hwj
      · subst hwj
        have h1 : (depths h ⟨resF.1, 0⟩).getD (resF.2 ∅) 0 ≤ du + width + (held j).toList.length := hdepF ∅ (Finset.empty_subset _)
        rw [hdep_j]
        have : (2 * width + 1) * (1 + (depths (2 * k) D).getD u 0) =
            du + (2 * width + 1) := by dsimp [du]; ring
        omega
      · rw [hext_all, depths_append_getD_old (hfin_lt w (by omega))]
        exact hfin_dep w (by omega)
    · intro Y w hw A hA hv
      dsimp only at hv; split_ifs at hv with hwj
      · subst hwj
        rw [hextF, wires_append_getD_old (visInput_length Y) (hTj_lt A hA)] at hv
        obtain ⟨A0, hA0u, hA0eq, hA0v⟩ := (hvalU (visInput Y) (visInput_length Y)
          (A ∩ Su) (hSu_eq.symm ▸ Finset.inter_subset_right)).mp hv
        rw [hSu_eq] at hA0eq
        have hCu := htab_snd Y u hu_lt A0 hA0u hA0v
        obtain ⟨P, N, hP, hN, hPo, hdPN, hdP, hdN, hX⟩ := cert_on_sub hSu_sub hA0eq hCu
        have hPV : P ⊆ varsAt k D u := hP.trans (by unfold varsAt; exact Finset.subset_union_left)
        have hNV : N ⊆ varsAt k D u := hN.trans (by unfold varsAt; exact Finset.subset_union_right)
        have hlift := lift_disjoint_vars hPV hNV (B := held j) (S := Su) (by simp [Su, hBt_eq]) hA hdP hdN
        refine ⟨P, N, hP.trans hmu.1, hN.trans hmu.2, hPo, hdPN, hlift.1, hlift.2, ?_⟩
        intro X hPX hNX
        rw [wires_getD_gate hpos.1.2.1 (word_length X _) hm]
        change g.op.eval (g.inputs.map _) = true
        rcases hop with h_op | h_op <;> rw [h_op, hin] <;> simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, hX X hPX hNX] <;> rfl
      · rw [hext_all, wires_append_getD_old (visInput_length Y) (htab_lt w (by omega) A hA)] at hv
        exact htab_snd Y w (by omega) A hA hv
    · intro Y w hw hv
      dsimp only at hv; split_ifs at hv with hwj
      · subst hwj
        obtain ⟨A, hAj, _, hAv⟩ := (hvalF (visInput Y) (visInput_length Y) ∅ (Finset.empty_subset _)).mp hv
        obtain ⟨A0, hA0u, hA0eq, hA0v⟩ := (hvalU (visInput Y) (visInput_length Y)
          (A ∩ Su) (hSu_eq.symm ▸ Finset.inter_subset_right)).mp hAv
        rw [hSu_eq] at hA0eq
        have hCu := htab_snd Y u hu_lt A0 hA0u hA0v
        obtain ⟨P, N, hP, hN, hPo, hdPN, hdP, hdN, hX⟩ := cert_on_sub hSu_sub hA0eq hCu
        have hPV : P ⊆ varsAt k D u := hP.trans (by unfold varsAt; exact Finset.subset_union_left)
        have hNV : N ⊆ varsAt k D u := hN.trans (by unfold varsAt; exact Finset.subset_union_right)
        have hlift := lift_disjoint_vars hPV hNV (B := held j) (S := Su) (by simp [Su, hBt_eq]) hAj hdP hdN
        refine ⟨A, hAj, P, N, hP.trans hmu.1, hN.trans hmu.2, hPo, hdPN, hlift.1, hlift.2, ?_⟩
        intro X hPX hNX
        rw [wires_getD_gate hpos.1.2.1 (word_length X _) hm]
        change g.op.eval (g.inputs.map _) = true
        rcases hop with h_op | h_op <;> rw [h_op, hin] <;> simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, hX X hPX hNX] <;> rfl
      · rw [hext_all, wires_append_getD_old (visInput_length Y) (hfin_lt w (by omega))] at hv
        exact hfin_snd Y w (by omega) hv
    · intro Y X hXo w hw hv
      dsimp only; split_ifs with hwj
      · subst hwj
        rw [wires_getD_gate hpos.1.2.1 (word_length X _) hm] at hv
        have hvu : (D.wires (word X (Finset.univ \ X))).getD u false = true := by
          change g.op.eval (g.inputs.map _) = true at hv
          rcases hop with h_op | h_op <;> simpa [h_op, hin, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil] using hv
        have hcu := (hcomp Y X hXo u hu_lt hvu).1
        have hTj_true : (Circuit.wires ⟨resU.1, 0⟩ (visInput Y)).getD (Tj (X ∩ held j)) false = true := by
          apply (hvalU (visInput Y) (visInput_length Y) ((X ∩ held j) ∩ Su)
            (hSu_eq.symm ▸ Finset.inter_subset_right)).mpr
          refine ⟨X ∩ held u, Finset.inter_subset_right, ?_, hcu⟩
          rw [hSu_eq]
          ext z
          have hSubj : Su ⊆ held j := by simp [Su, hBt_eq]
          simp only [Finset.mem_inter]
          exact ⟨fun ⟨⟨hzX, _⟩, hzS⟩ => ⟨⟨hzX, hSubj hzS⟩, hzS⟩,
            fun ⟨⟨hzX, _⟩, hzS⟩ => ⟨⟨hzX, hSu_sub hzS⟩, hzS⟩⟩
        constructor
        · rw [hextF, wires_append_getD_old (visInput_length Y) (hTj_lt _ Finset.inter_subset_right)]
          exact hTj_true
        · apply (hvalF (visInput Y) (visInput_length Y) ∅ (Finset.empty_subset _)).mpr
          refine ⟨X ∩ held j, Finset.inter_subset_right, ?_, hTj_true⟩
          rw [sdiff_self_toList_eq]; simp
      · rw [hext_all, wires_append_getD_old (visInput_length Y) (htab_lt w (by omega) _ Finset.inter_subset_right),
          wires_append_getD_old (visInput_length Y) (hfin_lt w (by omega))]
        exact hcomp Y X hXo w (by omega) hv
  ·
    have hu_mem : u ∈ g.inputs := by rw [hin]; simp
    have hv_mem : v ∈ g.inputs := by rw [hin]; simp
    have hu_lt : u < src + m := hpos.1.2.1 m hm u hu_mem
    have hv_lt : v < src + m := hpos.1.2.1 m hm v hv_mem
    have hu_card : (held u).card ≤ width := hheld_card u (by omega)
    have hv_card : (held v).card ≤ width := hheld_card v (by omega)
    let Su := Bt ∩ varsAt k D u
    let Sv := Bt ∩ varsAt k D v
    have hSu_sub : Su ⊆ held u := hleg.2 m hm u hu_mem
    have hSv_sub : Sv ⊆ held v := hleg.2 m hm v hv_mem
    have hSu_eq : held u \ (held u \ Su).toList.toFinset = Su := sdiff_toList_eq (held u) Su hSu_sub
    have hSv_eq : held v \ (held v \ Sv).toList.toFinset = Sv := sdiff_toList_eq (held v) Sv hSv_sub
    let du := (2 * width + 1) * (depths (2 * k) D).getD u 0
    let dv := (2 * width + 1) * (depths (2 * k) D).getD v 0
    let resU := elimVars h (held u \ Su).toList (held u) st.gates (st.tab u)
    obtain ⟨⟨extU, hextU⟩, hlenU, hGU, hltU, hvalU, hdepU⟩ :=
      elimVars_spec h (held u \ Su).toList (held u) st.gates (st.tab u)
        (Finset.nodup_toList _) (fun x hx => (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1)
        hG (fun A hA => htab_lt u hu_lt A hA) du (fun A hA => htab_dep u hu_lt A hA)
    have hresU_len : resU.1.length ≤ st.gates.length + 2 ^ width :=
      (Nat.le_add_right _ _).trans (hlenU.le.trans (Nat.add_le_add_left (hpow_le (held u) hu_card) _))
    have htv_lt : ∀ A ⊆ held v, st.tab v A < h + 2 + resU.1.length := by
      intro A hA; have := htab_lt v hv_lt A hA; rw [hextU, List.length_append]; omega
    have htv_dep : ∀ A ⊆ held v, (depths h ⟨resU.1, 0⟩).getD (st.tab v A) 0 ≤ dv := by
      intro A hA; rw [hextU, depths_append_getD_old (htab_lt v hv_lt A hA)]; exact htab_dep v hv_lt A hA
    let resV := elimVars h (held v \ Sv).toList (held v) resU.1 (st.tab v)
    obtain ⟨⟨extV, hextV⟩, hlenV, hGV, hltV, hvalV, hdepV⟩ :=
      elimVars_spec h (held v \ Sv).toList (held v) resU.1 (st.tab v)
        (Finset.nodup_toList _) (fun x hx => (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1)
        hGU htv_lt dv htv_dep
    have hresV_len : resV.1.length ≤ resU.1.length + 2 ^ width :=
      (Nat.le_add_right _ _).trans (hlenV.le.trans (Nat.add_le_add_left (hpow_le (held v) hv_card) _))
    have hLmem : ∀ C, C ∈ Bt.powerset.toList ↔ C ⊆ Bt := by
      intro C; simp [Finset.mem_powerset]
    have hLlen : Bt.powerset.toList.length = 2 ^ Bt.card := by
      simp [Finset.length_toList, Finset.card_powerset]
    have hM_lt : ∀ C ∈ Bt.powerset.toList,
        resU.2 (C ∩ Su) < h + 2 + resV.1.length ∧ resV.2 (C ∩ Sv) < h + 2 + resV.1.length := by
      intro C _
      refine ⟨?_, hltV (C ∩ Sv) (hSv_eq.symm ▸ Finset.inter_subset_right)⟩
      have h1 : resU.2 (C ∩ Su) < h + 2 + resU.1.length := hltU (C ∩ Su) (hSu_eq.symm ▸ Finset.inter_subset_right)
      rw [hextV, List.length_append]; omega
    let resM := addBinBatch h g.op Bt.powerset.toList
      (fun C => resU.2 (C ∩ Su)) (fun C => resV.2 (C ∩ Sv)) resV.1
    obtain ⟨⟨extM, hextM⟩, hlenM, hGM, hltM, hvalM, hdepM⟩ :=
      addBinBatch_spec h g.op hop Bt.powerset.toList
        (fun C => resU.2 (C ∩ Su)) (fun C => resV.2 (C ∩ Sv)) resV.1 hGV hM_lt
    have hresM_len : resM.1.length ≤ resV.1.length + 2 ^ width := by
      have hp := hpow_le Bt hBt_card; change resM.1.length = resV.1.length + _ at hlenM; rw [hlenM, hLlen]; omega
    have hFu_len : (held u \ Su).toList.length ≤ width := by
      rw [Finset.length_toList]; exact (Finset.card_le_card Finset.sdiff_subset).trans hu_card
    have hFv_len : (held v \ Sv).toList.length ≤ width := by
      rw [Finset.length_toList]; exact (Finset.card_le_card Finset.sdiff_subset).trans hv_card
    have hM_dep : ∀ C ⊆ Bt, (depths h ⟨resM.1, 0⟩).getD (resM.2 C) 0 ≤ max du dv + width + 1 := by
      intro C hC
      have h1 : (depths h ⟨resM.1, 0⟩).getD (resM.2 C) 0 ≤ 1 + max ((depths h ⟨resV.1, 0⟩).getD (resU.2 (C ∩ Su)) 0) ((depths h ⟨resV.1, 0⟩).getD (resV.2 (C ∩ Sv)) 0) := hdepM C ((hLmem C).mpr hC)
      have hUold : (depths h ⟨resV.1, 0⟩).getD (resU.2 (C ∩ Su)) 0 = (depths h ⟨resU.1, 0⟩).getD (resU.2 (C ∩ Su)) 0 := by
        rw [hextV]; exact depths_append_getD_old (hltU (C ∩ Su) (hSu_eq.symm ▸ Finset.inter_subset_right))
      rw [hUold] at h1
      have hd1 : (depths h ⟨resU.1, 0⟩).getD (resU.2 (C ∩ Su)) 0 ≤ du + (held u \ Su).toList.length := hdepU (C ∩ Su) (hSu_eq.symm ▸ Finset.inter_subset_right)
      have hd2 : (depths h ⟨resV.1, 0⟩).getD (resV.2 (C ∩ Sv)) 0 ≤ dv + (held v \ Sv).toList.length := hdepV (C ∩ Sv) (hSv_eq.symm ▸ Finset.inter_subset_right)
      omega
    have hBt_hj : held j ⊆ Bt := Finset.subset_union_left
    have hJ_eq : Bt \ (Bt \ held j).toList.toFinset = held j := sdiff_toList_eq Bt (held j) hBt_hj
    let resJ := elimVars h (Bt \ held j).toList Bt resM.1 resM.2
    obtain ⟨⟨extJ, hextJ⟩, hlenJ, hGJ, hltJ, hvalJ, hdepJ⟩ :=
      elimVars_spec h (Bt \ held j).toList Bt resM.1 resM.2
        (Finset.nodup_toList _) (fun x hx => (Finset.mem_sdiff.mp (Finset.mem_toList.mp hx)).1)
        hGM (fun C hC => hltM C ((hLmem C).mpr hC)) (max du dv + width + 1) hM_dep
    have hresJ_len : resJ.1.length ≤ resM.1.length + 2 ^ width :=
      (Nat.le_add_right _ _).trans (hlenJ.le.trans (Nat.add_le_add_left (hpow_le Bt hBt_card) _))
    have hFJ_len : (Bt \ held j).toList.length ≤ width := by
      rw [Finset.length_toList]; exact (Finset.card_le_card Finset.sdiff_subset).trans hBt_card
    have hJ_dep : ∀ A ⊆ held j, (depths h ⟨resJ.1, 0⟩).getD (resJ.2 A) 0 ≤ max du dv + 2 * width + 1 := by
      intro A hA
      have hd : (depths h ⟨resJ.1, 0⟩).getD (resJ.2 A) 0 ≤ max du dv + width + 1 + (Bt \ held j).toList.length := hdepJ A (hJ_eq.symm ▸ hA)
      omega
    let resF := elimVars h (held j).toList (held j) resJ.1 resJ.2
    obtain ⟨⟨extF, hextF⟩, hlenF, hGF, hltF, hvalF, hdepF⟩ :=
      elimVars_spec h (held j).toList (held j) resJ.1 resJ.2
        (Finset.nodup_toList _) (fun x hx => Finset.mem_toList.mp hx)
        hGJ (fun A hA => hltJ A (hJ_eq.symm ▸ hA)) (max du dv + 2 * width + 1) hJ_dep
    have hresF_len : resF.1.length ≤ resJ.1.length + 2 ^ width :=
      (Nat.le_add_right _ _).trans (hlenF.le.trans (Nat.add_le_add_left (hpow_le (held j) hhj_card) _))
    have hFf_len : (held j).toList.length ≤ width := by
      rw [Finset.length_toList]; exact hhj_card
    have hext_all : resF.1 = st.gates ++ (extU ++ extV ++ extM ++ extJ ++ extF) := by
      rw [hextF, hextJ, hextM, hextV, hextU]; simp [List.append_assoc]
    have hcomp_eq : compileOneGate h D held m st =
        { gates := resF.1
          tab := fun w0 A => if w0 = j then resJ.2 A else st.tab w0 A
          finW := fun w0 => if w0 = j then resF.2 ∅ else st.finW w0 } := by
      unfold compileOneGate; simp [g, j, src, hin, Bt, Su, Sv, resU, resV, resM, resJ, resF]
    rw [hcomp_eq]
    have hdep_j : (depths (2 * k) D).getD j 0 =
        1 + max ((depths (2 * k) D).getD u 0) ((depths (2 * k) D).getD v 0) := by
      rw [depths_getD_gate hpos.1.2.1 hm]
      change 1 + g.inputs.foldl _ 0 = _
      simp [hin]
    have hmax_mul : max du dv + (2 * width + 1) = (2 * width + 1) * (depths (2 * k) D).getD j 0 := by
      rw [hdep_j]
      dsimp [du, dv]
      rcases le_total ((depths (2 * k) D).getD u 0) ((depths (2 * k) D).getD v 0) with hle | hle
      · rw [max_eq_right hle, max_eq_right (Nat.mul_le_mul_left _ hle)]; ring
      · rw [max_eq_left hle, max_eq_left (Nat.mul_le_mul_left _ hle)]; ring
    have hmu := wireInfo_mono hpos.1.2.1 hm hu_mem
    have hmv := wireInfo_mono hpos.1.2.1 hm hv_mem

    have hJ_snd : ∀ (Y : Finset (Fin h)) (A : Finset (Fin k)), A ⊆ held j →
        (Circuit.wires ⟨resJ.1, 0⟩ (visInput Y)).getD (resJ.2 A) false = true →
        CertAt e D held Y j A := by
      intro Y A hAj hJv
      obtain ⟨C, hCBt, hCeq, hMv⟩ := (hvalJ (visInput Y) (visInput_length Y) A (hJ_eq.symm ▸ hAj)).mp hJv
      rw [hJ_eq] at hCeq
      rw [hvalM (visInput Y) (visInput_length Y) C ((hLmem C).mpr hCBt)] at hMv
      have hUold := wires_append_getD_old (h := h) (B := resU.1) (extra := extV) (visInput_length Y)
        (hltU (C ∩ Su) (hSu_eq.symm ▸ Finset.inter_subset_right))
      rw [← hextV] at hUold
      rw [hUold] at hMv
      rcases hop with hand | hor
      · simp only [hand, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_true] at hMv
        obtain ⟨A1, hA1u, hA1eq, hA1v⟩ := (hvalU (visInput Y) (visInput_length Y)
          (C ∩ Su) (hSu_eq.symm ▸ Finset.inter_subset_right)).mp hMv.1
        rw [hSu_eq] at hA1eq
        obtain ⟨A2, hA2v, hA2eq, hA2v'⟩ := (hvalV (visInput Y) (visInput_length Y)
          (C ∩ Sv) (hSv_eq.symm ▸ Finset.inter_subset_right)).mp hMv.2
        rw [hSv_eq] at hA2eq
        rw [hextU, wires_append_getD_old (visInput_length Y) (htab_lt v hv_lt A2 hA2v)] at hA2v'
        obtain ⟨P1, N1, hP1, hN1, hP1o, hd1, hdP1, hdN1, hX1⟩ :=
          cert_on_sub hSu_sub hA1eq (htab_snd Y u hu_lt A1 hA1u hA1v)
        obtain ⟨P2, N2, hP2, hN2, hP2o, hd2, hdP2, hdN2, hX2⟩ :=
          cert_on_sub hSv_sub hA2eq (htab_snd Y v hv_lt A2 hA2v hA2v')
        have hL1 := lift_disjoint_vars (hP1.trans (by unfold varsAt; exact Finset.subset_union_left))
          (hN1.trans (by unfold varsAt; exact Finset.subset_union_right)) rfl hCBt hdP1 hdN1
        have hL2 := lift_disjoint_vars (hP2.trans (by unfold varsAt; exact Finset.subset_union_left))
          (hN2.trans (by unfold varsAt; exact Finset.subset_union_right)) rfl hCBt hdP2 hdN2
        have hcr_sub : (((wireInfo k D).getD u (∅, ∅)).1 ∩ ((wireInfo k D).getD v (∅, ∅)).2) ∪
            (((wireInfo k D).getD u (∅, ∅)).2 ∩ ((wireInfo k D).getD v (∅, ∅)).1) ⊆ Bt := by
          have hcr_eq : crossGate k D m =
              (((wireInfo k D).getD u (∅, ∅)).1 ∩ ((wireInfo k D).getD v (∅, ∅)).2) ∪
              (((wireInfo k D).getD u (∅, ∅)).2 ∩ ((wireInfo k D).getD v (∅, ∅)).1) := by
            unfold crossGate
            dsimp only
            change (if g.op = GateOp.and then (((g.inputs.head?.map (fun j => (wireInfo k D).getD j (∅, ∅))).getD (∅, ∅)).1 ∩
              ((g.inputs[1]?.map (fun j => (wireInfo k D).getD j (∅, ∅))).getD (∅, ∅)).2) ∪
              (((g.inputs.head?.map (fun j => (wireInfo k D).getD j (∅, ∅))).getD (∅, ∅)).2 ∩
              ((g.inputs[1]?.map (fun j => (wireInfo k D).getD j (∅, ∅))).getD (∅, ∅)).1) else ∅) = _
            rw [hand, hin]
            simp
          rw [← hcr_eq]; exact Finset.subset_union_right
        have hd12 : Disjoint P1 N2 := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have hxBt : x ∈ Bt := hcr_sub (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hP1 hx1, hN2 hx2⟩))
          by_cases hxC : x ∈ C
          · exact Finset.disjoint_left.mp hL2.2 hx2 hxC
          · exact Finset.disjoint_left.mp hL1.1 hx1 (Finset.mem_sdiff.mpr ⟨hxBt, hxC⟩)
        have hd21 : Disjoint P2 N1 := by
          rw [Finset.disjoint_left]
          intro x hx2 hx1
          have hxBt : x ∈ Bt := hcr_sub (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hN1 hx1, hP2 hx2⟩))
          by_cases hxC : x ∈ C
          · exact Finset.disjoint_left.mp hL1.2 hx1 hxC
          · exact Finset.disjoint_left.mp hL2.1 hx2 (Finset.mem_sdiff.mpr ⟨hxBt, hxC⟩)
        have hP_hj : Disjoint (P1 ∪ P2) (held j \ A) := by
          rw [Finset.disjoint_left]
          intro x hxP hxS
          have hxh := (Finset.mem_sdiff.mp hxS).1
          have hxnA := (Finset.mem_sdiff.mp hxS).2
          have hxnC : x ∉ C := fun hxC => hxnA (hCeq ▸ Finset.mem_inter.mpr ⟨hxC, hxh⟩)
          have hxBC : x ∈ Bt \ C := Finset.mem_sdiff.mpr ⟨hBt_hj hxh, hxnC⟩
          rcases Finset.mem_union.mp hxP with hx1 | hx2
          · exact Finset.disjoint_left.mp hL1.1 hx1 hxBC
          · exact Finset.disjoint_left.mp hL2.1 hx2 hxBC
        have hN_hj : Disjoint (N1 ∪ N2) A := by
          rw [Finset.disjoint_left]
          intro x hxN hxA
          have hxC : x ∈ C := (Finset.mem_inter.mp (hCeq.symm ▸ hxA)).1
          rcases Finset.mem_union.mp hxN with hx1 | hx2
          · exact Finset.disjoint_left.mp hL1.2 hx1 hxC
          · exact Finset.disjoint_left.mp hL2.2 hx2 hxC
        refine ⟨P1 ∪ P2, N1 ∪ N2,
          Finset.union_subset (hP1.trans hmu.1) (hP2.trans hmv.1),
          Finset.union_subset (hN1.trans hmu.2) (hN2.trans hmv.2),
          Finset.union_subset hP1o hP2o,
          Finset.disjoint_union_left.mpr
            ⟨Finset.disjoint_union_right.mpr ⟨hd1, hd12⟩,
             Finset.disjoint_union_right.mpr ⟨hd21, hd2⟩⟩,
          hP_hj, hN_hj, ?_⟩
        intro X hPX hNX
        rw [wires_getD_gate hpos.1.2.1 (word_length X _) hm]
        have h1 := hX1 X (Finset.subset_union_left.trans hPX) (Finset.disjoint_union_left.mp hNX).1
        have h2 := hX2 X (Finset.subset_union_right.trans hPX) (Finset.disjoint_union_left.mp hNX).2
        change g.op.eval (g.inputs.map _) = true
        rw [hand, hin]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, h1, h2]; rfl
      · simp only [hor, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true] at hMv
        rcases hMv with hMu | hMv'
        · obtain ⟨A1, hA1u, hA1eq, hA1v⟩ := (hvalU (visInput Y) (visInput_length Y)
            (C ∩ Su) (hSu_eq.symm ▸ Finset.inter_subset_right)).mp hMu
          rw [hSu_eq] at hA1eq
          obtain ⟨P1, N1, hP1, hN1, hP1o, hd1, hdP1, hdN1, hX1⟩ :=
            cert_on_sub hSu_sub hA1eq (htab_snd Y u hu_lt A1 hA1u hA1v)
          have hL1 := lift_disjoint_vars (hP1.trans (by unfold varsAt; exact Finset.subset_union_left))
            (hN1.trans (by unfold varsAt; exact Finset.subset_union_right)) rfl hCBt hdP1 hdN1
          refine ⟨P1, N1, hP1.trans hmu.1, hN1.trans hmu.2, hP1o, hd1, ?_, ?_, ?_⟩
          · rw [Finset.disjoint_left]
            intro x hx1 hxS
            have hxh := (Finset.mem_sdiff.mp hxS).1
            have hxnA := (Finset.mem_sdiff.mp hxS).2
            have hxnC : x ∉ C := fun hxC => hxnA (hCeq ▸ Finset.mem_inter.mpr ⟨hxC, hxh⟩)
            exact Finset.disjoint_left.mp hL1.1 hx1 (Finset.mem_sdiff.mpr ⟨hBt_hj hxh, hxnC⟩)
          · rw [Finset.disjoint_left]
            intro x hx1 hxA
            exact Finset.disjoint_left.mp hL1.2 hx1 (Finset.mem_inter.mp (hCeq.symm ▸ hxA)).1
          · intro X hPX hNX
            rw [wires_getD_gate hpos.1.2.1 (word_length X _) hm]
            change g.op.eval (g.inputs.map _) = true
            rw [hor, hin]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hX1 X hPX hNX, Bool.true_or]
        · obtain ⟨A2, hA2v, hA2eq, hA2v'⟩ := (hvalV (visInput Y) (visInput_length Y)
            (C ∩ Sv) (hSv_eq.symm ▸ Finset.inter_subset_right)).mp hMv'
          rw [hSv_eq] at hA2eq
          rw [hextU, wires_append_getD_old (visInput_length Y) (htab_lt v hv_lt A2 hA2v)] at hA2v'
          obtain ⟨P2, N2, hP2, hN2, hP2o, hd2, hdP2, hdN2, hX2⟩ :=
            cert_on_sub hSv_sub hA2eq (htab_snd Y v hv_lt A2 hA2v hA2v')
          have hL2 := lift_disjoint_vars (hP2.trans (by unfold varsAt; exact Finset.subset_union_left))
            (hN2.trans (by unfold varsAt; exact Finset.subset_union_right)) rfl hCBt hdP2 hdN2
          refine ⟨P2, N2, hP2.trans hmv.1, hN2.trans hmv.2, hP2o, hd2, ?_, ?_, ?_⟩
          · rw [Finset.disjoint_left]
            intro x hx2 hxS
            have hxh := (Finset.mem_sdiff.mp hxS).1
            have hxnA := (Finset.mem_sdiff.mp hxS).2
            have hxnC : x ∉ C := fun hxC => hxnA (hCeq ▸ Finset.mem_inter.mpr ⟨hxC, hxh⟩)
            exact Finset.disjoint_left.mp hL2.1 hx2 (Finset.mem_sdiff.mpr ⟨hBt_hj hxh, hxnC⟩)
          · rw [Finset.disjoint_left]
            intro x hx2 hxA
            exact Finset.disjoint_left.mp hL2.2 hx2 (Finset.mem_inter.mp (hCeq.symm ▸ hxA)).1
          · intro X hPX hNX
            rw [wires_getD_gate hpos.1.2.1 (word_length X _) hm]
            change g.op.eval (g.inputs.map _) = true
            rw [hor, hin]; simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, hX2 X hPX hNX, Bool.or_false, Bool.or_true]
    refine ⟨hGF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change resF.1.length ≤ 5 * 2 ^ width * (m + 1)
      have : 5 * 2 ^ width * (m + 1) = 5 * 2 ^ width * m + 5 * 2 ^ width := by ring
      omega
    · intro w hw A hA
      dsimp only; split_ifs with hwj
      · subst hwj
        have h1 : resJ.2 A < h + 2 + resJ.1.length := hltJ A (hJ_eq.symm ▸ hA)
        change resJ.2 A < h + 2 + resF.1.length
        rw [hextF, List.length_append]; omega
      · have h1 := htab_lt w (by omega) A hA
        rw [hext_all, List.length_append]; omega
    · intro w hw
      dsimp only; split_ifs with hwj
      · subst hwj
        exact hltF ∅ (Finset.empty_subset _)
      · have h1 := hfin_lt w (by omega)
        rw [hext_all, List.length_append]; omega
    · intro w hw A hA
      dsimp only; split_ifs with hwj
      · subst hwj
        rw [hextF, depths_append_getD_old (hltJ A (hJ_eq.symm ▸ hA))]
        have h1 : (depths h ⟨resJ.1, 0⟩).getD (resJ.2 A) 0 ≤ max du dv + 2 * width + 1 := hJ_dep A hA
        rw [← hmax_mul]
        omega
      · rw [hext_all, depths_append_getD_old (htab_lt w (by omega) A hA)]
        exact htab_dep w (by omega) A hA
    · intro w hw
      dsimp only; split_ifs with hwj
      · subst hwj
        have h1 : (depths h ⟨resF.1, 0⟩).getD (resF.2 ∅) 0 ≤ max du dv + 2 * width + 1 + (held j).toList.length := hdepF ∅ (Finset.empty_subset _)
        rw [← hmax_mul]
        omega
      · rw [hext_all, depths_append_getD_old (hfin_lt w (by omega))]
        exact hfin_dep w (by omega)
    · intro Y w hw A hA hv
      dsimp only at hv; split_ifs at hv with hwj
      · subst hwj
        rw [hextF, wires_append_getD_old (visInput_length Y) (hltJ A (hJ_eq.symm ▸ hA))] at hv
        exact hJ_snd Y A hA hv
      · rw [hext_all, wires_append_getD_old (visInput_length Y) (htab_lt w (by omega) A hA)] at hv
        exact htab_snd Y w (by omega) A hA hv
    · intro Y w hw hv
      dsimp only at hv; split_ifs at hv with hwj
      · subst hwj
        obtain ⟨A, hAj, _, hAv⟩ := (hvalF (visInput Y) (visInput_length Y) ∅ (Finset.empty_subset _)).mp hv
        exact ⟨A, hAj, hJ_snd Y A hAj hAv⟩
      · rw [hext_all, wires_append_getD_old (visInput_length Y) (hfin_lt w (by omega))] at hv
        exact hfin_snd Y w (by omega) hv
    · intro Y X hXo w hw hv
      dsimp only; split_ifs with hwj
      · subst hwj
        rw [wires_getD_gate hpos.1.2.1 (word_length X _) hm] at hv
        let C := X ∩ Bt
        have hCBt : C ⊆ Bt := Finset.inter_subset_right
        have hSu_true : (D.wires (word X (Finset.univ \ X))).getD u false = true →
            (Circuit.wires ⟨resU.1, 0⟩ (visInput Y)).getD (resU.2 (C ∩ Su)) false = true := by
          intro hvu
          have hcu := (hcomp Y X hXo u hu_lt hvu).1
          apply (hvalU (visInput Y) (visInput_length Y) (C ∩ Su)
            (hSu_eq.symm ▸ Finset.inter_subset_right)).mpr
          refine ⟨X ∩ held u, Finset.inter_subset_right, ?_, hcu⟩
          rw [hSu_eq]
          ext z
          simp only [C, Finset.mem_inter]
          have hSub : Su ⊆ Bt := Finset.inter_subset_left
          exact ⟨fun ⟨⟨hzX, _⟩, hzS⟩ => ⟨⟨hzX, hSub hzS⟩, hzS⟩,
            fun ⟨⟨hzX, _⟩, hzS⟩ => ⟨⟨hzX, hSu_sub hzS⟩, hzS⟩⟩
        have hSv_true : (D.wires (word X (Finset.univ \ X))).getD v false = true →
            (Circuit.wires ⟨resV.1, 0⟩ (visInput Y)).getD (resV.2 (C ∩ Sv)) false = true := by
          intro hvv
          have hcv := (hcomp Y X hXo v hv_lt hvv).1
          apply (hvalV (visInput Y) (visInput_length Y) (C ∩ Sv)
            (hSv_eq.symm ▸ Finset.inter_subset_right)).mpr
          refine ⟨X ∩ held v, Finset.inter_subset_right, ?_, ?_⟩
          · rw [hSv_eq]
            ext z
            simp only [C, Finset.mem_inter]
            have hSub : Sv ⊆ Bt := Finset.inter_subset_left
            exact ⟨fun ⟨⟨hzX, _⟩, hzS⟩ => ⟨⟨hzX, hSub hzS⟩, hzS⟩,
              fun ⟨⟨hzX, _⟩, hzS⟩ => ⟨⟨hzX, hSv_sub hzS⟩, hzS⟩⟩
          · rw [hextU, wires_append_getD_old (visInput_length Y)
              (htab_lt v hv_lt _ Finset.inter_subset_right)]
            exact hcv
        have hM_true : (Circuit.wires ⟨resM.1, 0⟩ (visInput Y)).getD (resM.2 C) false = true := by
          rw [hvalM (visInput Y) (visInput_length Y) C ((hLmem C).mpr hCBt)]
          have hUold := wires_append_getD_old (h := h) (B := resU.1) (extra := extV) (visInput_length Y)
            (hltU (C ∩ Su) (hSu_eq.symm ▸ Finset.inter_subset_right))
          rw [← hextV] at hUold
          rw [hUold]
          change g.op.eval (g.inputs.map _) = true at hv
          rcases hop with hand | hor
          · simp only [hand, hin, List.map_cons, List.map_nil, GateOp.eval,
              List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_eq_true] at hv ⊢
            exact ⟨hSu_true hv.1, hSv_true hv.2⟩
          · simp only [hor, hin, List.map_cons, List.map_nil, GateOp.eval,
              List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true] at hv ⊢
            rcases hv with hvu | hvv
            · exact Or.inl (hSu_true hvu)
            · exact Or.inr (hSv_true hvv)
        have hJ_true : (Circuit.wires ⟨resJ.1, 0⟩ (visInput Y)).getD (resJ.2 (X ∩ held j)) false = true := by
          apply (hvalJ (visInput Y) (visInput_length Y) (X ∩ held j)
            (hJ_eq.symm ▸ Finset.inter_subset_right)).mpr
          refine ⟨C, hCBt, ?_, hM_true⟩
          rw [hJ_eq]
          ext z
          simp only [C, Finset.mem_inter]
          exact ⟨fun ⟨⟨hzX, _⟩, hzh⟩ => ⟨hzX, hzh⟩, fun ⟨hzX, hzh⟩ => ⟨⟨hzX, hBt_hj hzh⟩, hzh⟩⟩
        constructor
        · rw [hextF, wires_append_getD_old (visInput_length Y)
            (hltJ (X ∩ held j) (hJ_eq.symm ▸ Finset.inter_subset_right))]
          exact hJ_true
        · apply (hvalF (visInput Y) (visInput_length Y) ∅ (Finset.empty_subset _)).mpr
          refine ⟨X ∩ held j, Finset.inter_subset_right, ?_, hJ_true⟩
          rw [sdiff_self_toList_eq]; simp
      · rw [hext_all, wires_append_getD_old (visInput_length Y)
            (htab_lt w (by omega) _ Finset.inter_subset_right),
          wires_append_getD_old (visInput_length Y) (hfin_lt w (by omega))]
        exact hcomp Y X hXo w (by omega) hv

lemma compileUpTo_inv {h k : Nat} {e : Fin h → Fin k}
    (he : Function.Injective e) {D : Circuit} (hpos : pos (2 * k) D)
    {held : Nat → Finset (Fin k)} {width : Nat}
    (hleg : (∀ j < 2 * k + 2 + D.size, held j ⊆ varsAt k D j) ∧
      ∀ t < D.size, ∀ u ∈ (gateAt D t).inputs,
        (held (2 * k + 2 + t) ∪ crossGate k D t) ∩ varsAt k D u ⊆ held u)
    (hbnd : (∀ j < 2 * k + 2, (held j).card ≤ width) ∧
      ∀ t < D.size, (held (2 * k + 2 + t) ∪ crossGate k D t).card ≤ width) :
    ∀ m ≤ D.size, CompInv e D held width m (compileUpTo e D held m) := by
  intro m
  induction m with
  | zero => intro _; exact initComp_inv he held width
  | succ m ih =>
    intro hm
    exact compileOneGate_inv hpos hleg hbnd (by omega) (ih (by omega))

end WidthCompile

section MainParts

lemma part1_realizes_to_verifier0
    (h n g deadline : Nat) (f : Fin n → Finset (Fin h) → Bool)
    (E : Circuit) (out : Fin n → Nat)
    (hposE : pos h E) (hszE : E.size ≤ g)
    (hout : ∀ i, out i < h + 2 + E.size ∧ (depths h E).getD (out i) 0 ≤ deadline ∧
      ∀ Y : Finset (Fin h), (E.wires (visInput Y)).getD (out i) false = f i Y) :
    ∃ (k : Nat) (e : Fin h → Fin k) (D : Circuit) (outD : Fin n → Nat) (held : Nat → Finset (Fin k)),
      Function.Injective e ∧ pos (2 * k) D ∧ D.size ≤ g ∧
      ((∀ j < 2 * k + 2 + D.size, held j ⊆ varsAt k D j) ∧
       ∀ t < D.size, ∀ j ∈ (gateAt D t).inputs,
         (held (2 * k + 2 + t) ∪ crossGate k D t) ∩ varsAt k D j ⊆ held j) ∧
      ((∀ j < 2 * k + 2, (held j).card ≤ 0) ∧
       ∀ t < D.size, (held (2 * k + 2 + t) ∪ crossGate k D t).card ≤ 0) ∧
      ∀ i, outD i < 2 * k + 2 + D.size ∧ (depths (2 * k) D).getD (outD i) 0 ≤ deadline ∧
        ∀ Y : Finset (Fin h), f i Y = true ↔ ∃ X : Finset (Fin k),
          (∀ a : Fin h, e a ∈ X ↔ a ∈ Y) ∧
          (D.wires (word X (Finset.univ \ X))).getD (outD i) false = true := by
  let ρ : Nat → Nat := fun w =>
    if w < h then w
    else if w = h then 2 * h
    else if w = h + 1 then 2 * h + 1
    else 2 * h + 2 + (w - (h + 2))
  have hρ_in : ∀ j < h + 2, ρ j < 2 * h + 2 := by
    intro j hj; dsimp [ρ]; split_ifs <;> omega
  have hρ_gate : ∀ t < E.size, ρ (h + 2 + t) = 2 * h + 2 + t := by
    intro t _; dsimp [ρ]; split_ifs <;> omega
  let D := remapCircuit E ρ
  have hposD : pos (2 * h) D := remapCircuit_pos hposE ρ hρ_in hρ_gate
  have hszD : D.size = E.size := remapCircuit_size E ρ
  have hneg_empty : ∀ w < 2 * h + 2 + D.size, ¬ (h ≤ w ∧ w < 2 * h) →
      ((wireInfo h D).getD w (∅, ∅)).2 = ∅ := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hnot
      by_cases h1 : w < h
      · rw [wireInfo_getD_pos h D ⟨w, h1⟩]
      · by_cases h2 : w < 2 * h
        · exact absurd ⟨by omega, h2⟩ hnot
        · by_cases h3 : w = 2 * h
          · subst h3; rw [wireInfo_getD_const0 h D]
          · by_cases h4 : w = 2 * h + 1
            · subst h4; rw [wireInfo_getD_const1 h D]
            · obtain ⟨t, rfl⟩ : ∃ t, w = 2 * h + 2 + t := ⟨w - (2 * h + 2), by omega⟩
              have ht : t < D.size := by omega
              have htE : t < E.size := by omega
              rw [wireInfo_getD_gate hposD.1.2.1 ht, remapCircuit_gateAt E ρ htE]
              have hfold : ∀ (l : List Nat) (acc : Finset (Fin h) × Finset (Fin h)),
                  acc.2 = ∅ → (∀ u ∈ l, u < h + 2 + t) →
                  ((l.map ρ).foldl (fun v u =>
                    let a := (wireInfo h D).getD u (∅, ∅); (v.1 ∪ a.1, v.2 ∪ a.2)) acc).2 = ∅ := by
                intro l
                induction l with
                | nil => intro acc hacc _; exact hacc
                | cons a as ihl =>
                  intro acc hacc hall
                  simp only [List.map_cons, List.foldl_cons]
                  have ha := hall a (List.mem_cons_self ..)
                  have hρa_lt : ρ a < 2 * h + 2 + t := by
                    by_cases hlt : a < h + 2
                    · have := hρ_in a hlt; omega
                    · obtain ⟨s, rfl⟩ : ∃ s, a = h + 2 + s := ⟨a - (h + 2), by omega⟩
                      rw [hρ_gate s (by omega)]; omega
                  have hρa_not : ¬ (h ≤ ρ a ∧ ρ a < 2 * h) := by
                    dsimp [ρ]; split_ifs <;> omega
                  have ha2 : ((wireInfo h D).getD (ρ a) (∅, ∅)).2 = ∅ :=
                    ih (ρ a) hρa_lt (by omega) hρa_not
                  exact ihl _ (by dsimp only; rw [hacc, ha2]; simp) (fun u hu => hall u (List.mem_cons_of_mem a hu))
              exact hfold _ (∅, ∅) rfl (fun u hu => hposE.1.2.1 t htE u hu)
  have hcross0 : ∀ t < D.size, crossGate h D t = ∅ := by
    intro t ht
    have htE : t < E.size := by omega
    unfold crossGate
    dsimp only
    rw [remapCircuit_gateAt E ρ htE]
    dsimp only
    split_ifs with hand
    · have hhead : ((((gateAt E t).inputs.map ρ).head?.map
          (fun j => (wireInfo h D).getD j (∅, ∅))).getD (∅, ∅)).2 = ∅ := by
        cases hin : (gateAt E t).inputs with
        | nil => simp
        | cons a as =>
          simp only [List.map_cons, List.head?_cons, Option.map_some, Option.getD_some]
          have ha : a < h + 2 + t := hposE.1.2.1 t htE a (by rw [hin]; simp)
          have hρa_lt : ρ a < 2 * h + 2 + D.size := by
            by_cases hlt : a < h + 2
            · have := hρ_in a hlt; omega
            · obtain ⟨s, rfl⟩ : ∃ s, a = h + 2 + s := ⟨a - (h + 2), by omega⟩
              rw [hρ_gate s (by omega)]; omega
          exact hneg_empty (ρ a) hρa_lt (by dsimp [ρ]; split_ifs <;> omega)
      have hsnd : ((((gateAt E t).inputs.map ρ)[1]?.map
          (fun j => (wireInfo h D).getD j (∅, ∅))).getD (∅, ∅)).2 = ∅ := by
        cases hin : (gateAt E t).inputs with
        | nil => simp
        | cons a as =>
          cases as with
          | nil => simp
          | cons b bs =>
            simp only [List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.map_some, Option.getD_some]
            have hb : b < h + 2 + t := hposE.1.2.1 t htE b (by rw [hin]; simp)
            have hρb_lt : ρ b < 2 * h + 2 + D.size := by
              by_cases hlt : b < h + 2
              · have := hρ_in b hlt; omega
              · obtain ⟨s, rfl⟩ : ∃ s, b = h + 2 + s := ⟨b - (h + 2), by omega⟩
                rw [hρ_gate s (by omega)]; omega
            exact hneg_empty (ρ b) hρb_lt (by dsimp [ρ]; split_ifs <;> omega)
      rw [hhead, hsnd]; simp
    · rfl
  refine ⟨h, id, D, fun i => ρ (out i), fun _ => ∅, Function.injective_id, hposD, by omega,
    ⟨fun _ _ => Finset.empty_subset _, fun t ht _ _ => by simp [hcross0 t ht]⟩,
    ⟨fun _ _ => by simp, fun t ht => by simp [hcross0 t ht]⟩, ?_⟩
  intro i
  obtain ⟨hout_lt, hout_dep, hout_val⟩ := hout i
  have hρout_lt : ρ (out i) < 2 * h + 2 + D.size := by
    rw [hszD]
    by_cases hlt : out i < h + 2
    · have := hρ_in (out i) hlt; omega
    · obtain ⟨s, hs⟩ : ∃ s, out i = h + 2 + s := ⟨out i - (h + 2), by omega⟩
      rw [hs, hρ_gate s (by omega)]; omega
  refine ⟨hρout_lt, ?_, ?_⟩
  · rw [remapCircuit_depths hposE ρ hρ_in hρ_gate (out i) hout_lt]; exact hout_dep
  · intro Y
    have hmatch : ∀ j < h + 2, (word Y (Finset.univ \ Y)).getD (ρ j) false = (visInput Y).getD j false := by
      intro j hj
      by_cases h1 : j < h
      · have hρj : ρ j = j := by dsimp [ρ]; simp [h1]
        rw [hρj, word_getD_pos Y (Finset.univ \ Y) ⟨j, h1⟩, visInput_getD_var Y ⟨j, h1⟩]
      · by_cases h2 : j = h
        · subst h2
          have hρj : ρ j = 2 * j := by dsimp [ρ]; simp
          rw [hρj, word_getD_const0, visInput_getD_const0]
        · have h3 : j = h + 1 := by omega
          subst h3
          have hρj : ρ (h + 1) = 2 * h + 1 := by dsimp [ρ]; split_ifs <;> omega
          rw [hρj, word_getD_const1, visInput_getD_const1]
    have hw_eq := remapCircuit_wires hposE ρ hρ_in hρ_gate
      (visInput_length Y) (word_length Y (Finset.univ \ Y)) hmatch (out i) hout_lt
    rw [hout_val Y] at hw_eq
    constructor
    · intro hf
      exact ⟨Y, fun a => Iff.rfl, hw_eq.trans hf⟩
    · rintro ⟨X, hXY, hv⟩
      have hXeq : X = Y := by ext a; exact hXY a
      subst hXeq
      exact hw_eq.symm.trans hv

lemma part2_verifier0_to_realizes
    (h n g deadline : Nat) (f : Fin n → Finset (Fin h) → Bool)
    (hmono : ∀ i X Y, X ⊆ Y → f i X = true → f i Y = true)
    (k : Nat) (e : Fin h → Fin k) (D : Circuit) (out : Fin n → Nat) (held : Nat → Finset (Fin k))
    (he : Function.Injective e) (hposD : pos (2 * k) D) (hszD : D.size ≤ g)
    (hbnd : (∀ j < 2 * k + 2, (held j).card ≤ 0) ∧
      ∀ t < D.size, (held (2 * k + 2 + t) ∪ crossGate k D t).card ≤ 0)
    (hout : ∀ i, out i < 2 * k + 2 + D.size ∧ (depths (2 * k) D).getD (out i) 0 ≤ deadline ∧
      ∀ Y : Finset (Fin h), f i Y = true ↔ ∃ X : Finset (Fin k),
        (∀ a : Fin h, e a ∈ X ↔ a ∈ Y) ∧
        (D.wires (word X (Finset.univ \ X))).getD (out i) false = true) :
    ∃ (E : Circuit) (outE : Fin n → Nat), pos h E ∧ E.size ≤ g ∧ ∀ i,
      outE i < h + 2 + E.size ∧ (depths h E).getD (outE i) 0 ≤ deadline ∧
      ∀ Y : Finset (Fin h), (E.wires (visInput Y)).getD (outE i) false = f i Y := by
  have hcross0 : ∀ t < D.size, crossGate k D t = ∅ := by
    intro t ht
    have hc := hbnd.2 t ht
    have h0 : (held (2 * k + 2 + t) ∪ crossGate k D t).card = 0 := Nat.eq_zero_of_le_zero hc
    have heq := Finset.card_eq_zero.mp h0
    exact (Finset.union_eq_empty.mp heq).2
  let ρ : Nat → Nat := fun w =>
    if h1 : w < k then litWire e ⟨w, h1⟩
    else if w < 2 * k then h + 1
    else if w = 2 * k then h
    else if w = 2 * k + 1 then h + 1
    else h + 2 + (w - (2 * k + 2))
  have hρ_in : ∀ j < 2 * k + 2, ρ j < h + 2 := by
    intro j hj; dsimp [ρ]
    split_ifs <;> first | exact litWire_lt e _ | omega
  have hρ_gate : ∀ t < D.size, ρ (2 * k + 2 + t) = h + 2 + t := by
    intro t _; dsimp [ρ]; split_ifs <;> omega
  let E := remapCircuit D ρ
  have hposE : pos h E := remapCircuit_pos hposD ρ hρ_in hρ_gate
  have hszE : E.size = D.size := remapCircuit_size D ρ
  refine ⟨E, fun i => ρ (out i), hposE, by omega, ?_⟩
  intro i
  obtain ⟨hout_lt, hout_dep, hout_iff⟩ := hout i
  have hρout_lt : ρ (out i) < h + 2 + E.size := by
    rw [hszE]
    by_cases hlt : out i < 2 * k + 2
    · have := hρ_in (out i) hlt; omega
    · obtain ⟨s, hs⟩ : ∃ s, out i = 2 * k + 2 + s := ⟨out i - (2 * k + 2), by omega⟩
      rw [hs, hρ_gate s (by omega)]; omega
  refine ⟨hρout_lt, ?_, ?_⟩
  · rw [remapCircuit_depths hposD ρ hρ_in hρ_gate (out i) hout_lt]; exact hout_dep
  · intro Y
    have hmatch : ∀ j < 2 * k + 2,
        (visInput Y).getD (ρ j) false = (word (onesOf e Y) Finset.univ).getD j false := by
      intro j hj
      by_cases h1 : j < k
      · have hρj : ρ j = litWire e ⟨j, h1⟩ := by dsimp [ρ]; simp [h1]
        rw [hρj, litWire_val he Y ⟨j, h1⟩, word_getD_pos _ _ ⟨j, h1⟩]
      · by_cases h2 : j < 2 * k
        · have hρj : ρ j = h + 1 := by dsimp [ρ]; simp [h1, h2]
          let r : Fin k := ⟨j - k, by omega⟩
          have hjr : j = k + r.val := by simp [r]; omega
          rw [hρj, visInput_getD_const1, hjr, word_getD_neg]
          simp
        · by_cases h3 : j = 2 * k
          · subst h3
            have hρj : ρ (2 * k) = h := by dsimp [ρ]; split_ifs <;> omega
            rw [hρj, visInput_getD_const0, word_getD_const0]
          · have h4 : j = 2 * k + 1 := by omega
            subst h4
            have hρj : ρ (2 * k + 1) = h + 1 := by dsimp [ρ]; split_ifs <;> omega
            rw [hρj, visInput_getD_const1, word_getD_const1]
    have hEval := remapCircuit_wires hposD ρ hρ_in hρ_gate
      (word_length (onesOf e Y) Finset.univ) (visInput_length Y) hmatch (out i) hout_lt
    rw [hEval]
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hval
      obtain ⟨P, N, _, _, hPo, _, hdisj, hX⟩ :=
        zeroCross_cert hposD hcross0 (onesOf e Y) Finset.univ (out i) hout_lt hval
      have hPval := hX P (Finset.Subset.refl P) hdisj.symm
      let Y' : Finset (Fin h) := Finset.univ.filter (fun a => e a ∈ P)
      have hY'f : f i Y' = true := (hout_iff Y').mpr ⟨P, fun a => by simp [Y'], hPval⟩
      have hY'sub : Y' ⊆ Y := by
        intro a ha
        have heaP : e a ∈ P := (Finset.mem_filter.mp ha).2
        have heaO : e a ∈ onesOf e Y := hPo heaP
        rcases Finset.mem_union.mp heaO with hpriv | himg
        · exfalso
          exact (Finset.mem_sdiff.mp hpriv).2 (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
        · obtain ⟨b, hbY, hbe⟩ := Finset.mem_image.mp himg
          have hba : b = a := he hbe
          rwa [← hba]
      exact hmono i Y' Y hY'sub hY'f
    · intro hf
      obtain ⟨X, hXY, hXval⟩ := (hout_iff Y).mp hf
      have hXo : X ⊆ onesOf e Y := by
        intro x hxX
        by_cases himg : ∃ a : Fin h, e a = x
        · obtain ⟨a, rfl⟩ := himg
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, (hXY a).mp hxX, rfl⟩)
        · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, ?_⟩)
          simpa using himg
      apply wires_mono hposD (word_length X (Finset.univ \ X)) (word_length (onesOf e Y) Finset.univ)
        _ (out i) hout_lt hXval
      intro j hj hxj
      by_cases h1 : j < k
      · rw [word_getD_pos X (Finset.univ \ X) ⟨j, h1⟩] at hxj
        rw [word_getD_pos (onesOf e Y) Finset.univ ⟨j, h1⟩]
        have : (⟨j, h1⟩ : Fin k) ∈ X := by simpa using hxj
        simpa using hXo this
      · by_cases h2 : j < 2 * k
        · let r : Fin k := ⟨j - k, by omega⟩
          have hjr : j = k + r.val := by simp [r]; omega
          rw [hjr, word_getD_neg]; simp
        · by_cases h3 : j = 2 * k
          · subst h3; rw [word_getD_const0] at hxj; cases hxj
          · have h4 : j = 2 * k + 1 := by omega
            subst h4; rw [word_getD_const1]

lemma part3_verifierW_to_realizes
    (h n g deadline width : Nat) (f : Fin n → Finset (Fin h) → Bool)
    (hmono : ∀ i X Y, X ⊆ Y → f i X = true → f i Y = true)
    (k : Nat) (e : Fin h → Fin k) (D : Circuit) (out : Fin n → Nat) (held : Nat → Finset (Fin k))
    (he : Function.Injective e) (hposD : pos (2 * k) D) (hszD : D.size ≤ g)
    (hleg : (∀ j < 2 * k + 2 + D.size, held j ⊆ varsAt k D j) ∧
      ∀ t < D.size, ∀ u ∈ (gateAt D t).inputs,
        (held (2 * k + 2 + t) ∪ crossGate k D t) ∩ varsAt k D u ⊆ held u)
    (hbnd : (∀ j < 2 * k + 2, (held j).card ≤ width) ∧
      ∀ t < D.size, (held (2 * k + 2 + t) ∪ crossGate k D t).card ≤ width)
    (hout : ∀ i, out i < 2 * k + 2 + D.size ∧ (depths (2 * k) D).getD (out i) 0 ≤ deadline ∧
      ∀ Y : Finset (Fin h), f i Y = true ↔ ∃ X : Finset (Fin k),
        (∀ a : Fin h, e a ∈ X ↔ a ∈ Y) ∧
        (D.wires (word X (Finset.univ \ X))).getD (out i) false = true) :
    ∃ (E : Circuit) (outE : Fin n → Nat), pos h E ∧ E.size ≤ 13 * 2 ^ width * g ∧ ∀ i,
      outE i < h + 2 + E.size ∧
      (depths h E).getD (outE i) 0 ≤ (4 * width + 1) * deadline + 2 * width ∧
      ∀ Y : Finset (Fin h), (E.wires (visInput Y)).getD (outE i) false = f i Y := by
  let st := compileUpTo e D held D.size
  obtain ⟨hG, hlen, _, hfin_lt, _, hfin_dep, _, hfin_snd, hcomp⟩ :=
    compileUpTo_inv he hposD hleg hbnd D.size (Nat.le_refl _)
  refine ⟨⟨st.gates, 0⟩, fun i => st.finW (out i), goodGates_pos hG, ?_, ?_⟩
  · change st.gates.length ≤ 13 * 2 ^ width * g
    have hlen' : st.gates.length ≤ 5 * 2 ^ width * D.size := hlen
    have h1 : 5 * 2 ^ width * D.size ≤ 13 * 2 ^ width * D.size :=
      Nat.mul_le_mul_right D.size (Nat.mul_le_mul_right (2 ^ width) (by omega))
    have h2 : 13 * 2 ^ width * D.size ≤ 13 * 2 ^ width * g :=
      Nat.mul_le_mul_left _ hszD
    omega
  · intro i
    obtain ⟨hout_lt, hout_dep, hout_iff⟩ := hout i
    refine ⟨hfin_lt (out i) hout_lt, ?_, ?_⟩
    · change (depths h ⟨st.gates, 0⟩).getD (st.finW (out i)) 0 ≤ (4 * width + 1) * deadline + 2 * width
      have hd1 : (depths h ⟨st.gates, 0⟩).getD (st.finW (out i)) 0 ≤ (2 * width + 1) * (depths (2 * k) D).getD (out i) 0 + 2 * width := hfin_dep (out i) hout_lt
      have hd2 : (2 * width + 1) * (depths (2 * k) D).getD (out i) 0 ≤ (4 * width + 1) * deadline := by
        have ha : (2 * width + 1) * (depths (2 * k) D).getD (out i) 0 ≤ (2 * width + 1) * deadline :=
          Nat.mul_le_mul_left _ hout_dep
        have hb : (2 * width + 1) * deadline ≤ (4 * width + 1) * deadline :=
          Nat.mul_le_mul_right deadline (by omega)
        omega
      omega
    · intro Y
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hval
        obtain ⟨A, _, P, N, _, _, hPo, hdisj, _, _, hX⟩ := hfin_snd Y (out i) hout_lt hval
        have hPval := hX P (Finset.Subset.refl P) hdisj.symm
        let Y' : Finset (Fin h) := Finset.univ.filter (fun a => e a ∈ P)
        have hY'f : f i Y' = true := (hout_iff Y').mpr ⟨P, fun a => by simp [Y'], hPval⟩
        have hY'sub : Y' ⊆ Y := by
          intro a ha
          have heaP : e a ∈ P := (Finset.mem_filter.mp ha).2
          have heaO : e a ∈ onesOf e Y := hPo heaP
          rcases Finset.mem_union.mp heaO with hpriv | himg
          · exfalso
            exact (Finset.mem_sdiff.mp hpriv).2 (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
          · obtain ⟨b, hbY, hbe⟩ := Finset.mem_image.mp himg
            have hba : b = a := he hbe
            rwa [← hba]
        exact hmono i Y' Y hY'sub hY'f
      · intro hf
        obtain ⟨X, hXY, hXval⟩ := (hout_iff Y).mp hf
        have hXo : X ⊆ onesOf e Y := by
          intro x hxX
          by_cases himg : ∃ a : Fin h, e a = x
          · obtain ⟨a, rfl⟩ := himg
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, (hXY a).mp hxX, rfl⟩)
          · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, ?_⟩)
            simpa using himg
        exact (hcomp Y X hXo (out i) hout_lt hXval).2

end MainParts

end PEqualNP.Outside.L_lib_1482

theorem PEqualNP.Outside.L_lib_1482 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) D ∧ D.output < h+2+D.size
let pos := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => valid h D ∧ PEqualNP.NotBracket.notCount D=0
let word := fun {k : Nat} (ones zeros : Finset (Fin k)) =>
  List.ofFn (fun j : Fin k => decide (j ∈ ones)) ++
  List.ofFn (fun j : Fin k => decide (j ∈ zeros)) ++ [false,true]
let wireInfo := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let Z : Finset (Fin k) × Finset (Fin k) := (∅,∅)
  let xs := List.ofFn (fun j : Fin k => (({j},∅) : Finset (Fin k) × Finset (Fin k))) ++
    List.ofFn (fun j : Fin k => ((∅,{j}) : Finset (Fin k) × Finset (Fin k))) ++ [Z,Z]
  D.gates.foldl (fun (ts : List (Finset (Fin k) × Finset (Fin k))) g =>
    ts ++ [g.inputs.foldl (fun v t => let a := ts.getD t Z
                                      (v.1 ∪ a.1,v.2 ∪ a.2)) Z]) xs
let gateAt := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (t : Nat) => D.gates.getD t ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
let depths := fun (h : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  D.gates.foldl (fun (ts : List Nat) g =>
    ts ++ [1+g.inputs.foldl (fun m j => max m (ts.getD j 0)) 0]) (List.replicate (h+2) 0)
∀ (h n g deadline : Nat) (f : Fin n → Finset (Fin h) → Bool),
  (∀ i X Y, X ⊆ Y → f i X=true → f i Y=true) →
  let realizes := fun (G T : Nat) =>
    ∃ (E : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin n → Nat), pos h E ∧ E.size ≤ G ∧ ∀ i,
      out i < h+2+E.size ∧ (depths h E).getD (out i) 0 ≤ T ∧
      ∀ Y : Finset (Fin h),
        (E.wires (List.ofFn (fun j : Fin h => decide (j ∈ Y)) ++ [false,true])).getD (out i) false=f i Y
  let verifier := fun (width : Nat) =>
    ∃ (k : Nat) (e : Fin h → Fin k) (D : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin n → Nat) (held : Nat → Finset (Fin k)),
      Function.Injective e ∧ pos (2*k) D ∧ D.size ≤ g ∧
      let src := 2*k+2
      let Z : Finset (Fin k) × Finset (Fin k) := (∅,∅)
      let info := wireInfo k D
      let vars := fun (j : Nat) => let s := info.getD j Z
                                   s.1 ∪ s.2
      let cross := fun (t : Nat) =>
        let g := gateAt D t
        let a := (g.inputs.head?.map (fun j => info.getD j Z)).getD Z
        let b := (g.inputs[1]?.map (fun j => info.getD j Z)).getD Z
        if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then (a.1 ∩ b.2) ∪ (a.2 ∩ b.1) else ∅
      let legal := fun (B : Nat → Finset (Fin k)) =>
        (∀ j, j<src+D.size → B j ⊆ vars j) ∧
        ∀ t, t<D.size → ∀ j ∈ (gateAt D t).inputs, (B (src+t) ∪ cross t) ∩ vars j ⊆ B j
      let bounded := fun (w : Nat) (B : Nat → Finset (Fin k)) =>
        (∀ j, j<src → (B j).card ≤ w) ∧ ∀ t, t<D.size → (B (src+t) ∪ cross t).card ≤ w
      legal held ∧ bounded width held ∧ ∀ i,
        out i < src+D.size ∧ (depths (2*k) D).getD (out i) 0 ≤ deadline ∧
        ∀ Y : Finset (Fin h), f i Y=true ↔ ∃ X : Finset (Fin k),
          (∀ a : Fin h, e a ∈ X ↔ a ∈ Y) ∧
          (D.wires (word X (Finset.univ \ X))).getD (out i) false=true
  (realizes g deadline ↔ verifier 0) ∧ ∀ width : Nat, verifier width →
    realizes (13*2^width*g) ((4*width+1)*deadline+2*width)) := by
  intro valid pos word wireInfo gateAt depths h n g deadline f hmono realizes verifier
  have hWI : ∀ (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit),
      wireInfo k D = PEqualNP.Outside.L_lib_1482.wireInfo k D := by
    intro k D
    dsimp only [wireInfo, PEqualNP.Outside.L_lib_1482.wireInfo]
    congr 1
    funext ts g0
    apply congrArg (fun a => ts ++ [a])
    congr 1
    funext v t
    ext x <;> simp only [Finset.mem_union]
  have hVars : ∀ (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) (j : Nat),
      (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
       let s := (wireInfo k D).getD j (∅, ∅)
       s.1 ∪ s.2) =
        PEqualNP.Outside.L_lib_1482.varsAt k D j := by
    intro k D j
    rw [hWI k D]
    unfold PEqualNP.Outside.L_lib_1482.varsAt
    ext x
    simp only [Finset.mem_union]
  have hCross : ∀ (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) (t : Nat),
      (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
       let g0 := gateAt D t
       let a := (g0.inputs.head?.map (fun j => (wireInfo k D).getD j (∅, ∅))).getD (∅, ∅)
       let b := (g0.inputs[1]?.map (fun j => (wireInfo k D).getD j (∅, ∅))).getD (∅, ∅)
       if g0.op = PEqualNP.CircuitLowerBounds.GateOp.and then (a.1 ∩ b.2) ∪ (a.2 ∩ b.1) else ∅) =
        PEqualNP.Outside.L_lib_1482.crossGate k D t := by
    intro k D t
    rw [hWI k D]
    unfold PEqualNP.Outside.L_lib_1482.crossGate
    dsimp only [gateAt, PEqualNP.MetaComplexity.NestedCover.gateAt]
    by_cases hop : (D.gates.getD t ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = PEqualNP.CircuitLowerBounds.GateOp.and
    · rw [ite_eq_left hop, ite_eq_left hop]; ext x; simp only [Finset.mem_union, Finset.mem_inter]
    · rw [ite_eq_right hop, ite_eq_right hop]
  have hUnion : ∀ (k : Nat) (A B : Finset (Fin k)),
      (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable; A ∪ B) = A ∪ B := by
    intro k A B; ext x; simp only [Finset.mem_union]
  have hInter : ∀ (k : Nat) (A B : Finset (Fin k)),
      (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable; A ∩ B) = A ∩ B := by
    intro k A B; ext x; simp only [Finset.mem_inter]
  have hSDiff : ∀ (k : Nat) (X : Finset (Fin k)),
      (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable; Finset.univ \ X) =
      Finset.univ \ X := by
    intro k X; ext x; simp only [Finset.mem_sdiff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨E, out, hposE, hszE, hout⟩
    obtain ⟨k, e, D, outD, held, he, hposD, hszD, hleg, hbnd, houtD⟩ :=
      PEqualNP.Outside.L_lib_1482.part1_realizes_to_verifier0 h n g deadline f E out hposE hszE hout
    refine ⟨k, e, D, outD, held, he, hposD, hszD, ?_, ?_, ?_⟩
    · refine ⟨fun j hj => ?_, fun t ht j hj => ?_⟩
      · dsimp only; rw [hVars k D j]; exact hleg.1 j hj
      · dsimp only; rw [hCross k D t, hVars k D j, hUnion k, hInter k]; exact hleg.2 t ht j hj
    · refine ⟨hbnd.1, fun t ht => ?_⟩
      dsimp only; rw [hCross k D t, hUnion k]; exact hbnd.2 t ht
    · intro i
      obtain ⟨h1, h2, h3⟩ := houtD i
      refine ⟨h1, h2, fun Y => ?_⟩
      rw [h3 Y]
      constructor
      · rintro ⟨X, hXY, hv⟩; refine ⟨X, hXY, ?_⟩; rw [hSDiff k X]; exact hv
      · rintro ⟨X, hXY, hv⟩; refine ⟨X, hXY, ?_⟩; rw [hSDiff k X] at hv; exact hv
  · rintro ⟨k, e, D, out, held, he, hposD, hszD, _, hbnd, hout⟩
    have hbnd' : (∀ j < 2 * k + 2, (held j).card ≤ 0) ∧
        ∀ t < D.size, (held (2 * k + 2 + t) ∪ PEqualNP.Outside.L_lib_1482.crossGate k D t).card ≤ 0 := by
      refine ⟨hbnd.1, fun t ht => ?_⟩
      have h1 := hbnd.2 t ht
      dsimp only at h1
      rw [hCross k D t, hUnion k] at h1
      exact h1
    have hout' : ∀ i, out i < 2 * k + 2 + D.size ∧
        (PEqualNP.Outside.L_lib_1482.depths (2 * k) D).getD (out i) 0 ≤ deadline ∧
        ∀ Y : Finset (Fin h), f i Y = true ↔ ∃ X : Finset (Fin k),
          (∀ a : Fin h, e a ∈ X ↔ a ∈ Y) ∧
          (D.wires (PEqualNP.Outside.L_lib_1482.word X (Finset.univ \ X))).getD (out i) false = true := by
      intro i
      obtain ⟨h1, h2, h3⟩ := hout i
      refine ⟨h1, h2, fun Y => ?_⟩
      rw [h3 Y]
      constructor
      · rintro ⟨X, hXY, hv⟩; refine ⟨X, hXY, ?_⟩; rw [hSDiff k X] at hv; exact hv
      · rintro ⟨X, hXY, hv⟩; refine ⟨X, hXY, ?_⟩; rw [hSDiff k X]; exact hv
    exact PEqualNP.Outside.L_lib_1482.part2_verifier0_to_realizes h n g deadline f hmono k e D out held he hposD hszD hbnd' hout'
  · rintro width ⟨k, e, D, out, held, he, hposD, hszD, hleg, hbnd, hout⟩
    have hleg' : (∀ j < 2 * k + 2 + D.size, held j ⊆ PEqualNP.Outside.L_lib_1482.varsAt k D j) ∧
        ∀ t < D.size, ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D t).inputs,
          (held (2 * k + 2 + t) ∪ PEqualNP.Outside.L_lib_1482.crossGate k D t) ∩ PEqualNP.Outside.L_lib_1482.varsAt k D u ⊆ held u := by
      refine ⟨fun j hj => ?_, fun t ht u hu => ?_⟩
      · have h1 := hleg.1 j hj; dsimp only at h1; rwa [hVars k D j] at h1
      · have h1 := hleg.2 t ht u hu
        dsimp only at h1
        rw [hCross k D t, hVars k D u, hUnion k, hInter k] at h1
        exact h1
    have hbnd' : (∀ j < 2 * k + 2, (held j).card ≤ width) ∧
        ∀ t < D.size, (held (2 * k + 2 + t) ∪ PEqualNP.Outside.L_lib_1482.crossGate k D t).card ≤ width := by
      refine ⟨hbnd.1, fun t ht => ?_⟩
      have h1 := hbnd.2 t ht
      dsimp only at h1
      rw [hCross k D t, hUnion k] at h1
      exact h1
    have hout' : ∀ i, out i < 2 * k + 2 + D.size ∧
        (PEqualNP.Outside.L_lib_1482.depths (2 * k) D).getD (out i) 0 ≤ deadline ∧
        ∀ Y : Finset (Fin h), f i Y = true ↔ ∃ X : Finset (Fin k),
          (∀ a : Fin h, e a ∈ X ↔ a ∈ Y) ∧
          (D.wires (PEqualNP.Outside.L_lib_1482.word X (Finset.univ \ X))).getD (out i) false = true := by
      intro i
      obtain ⟨h1, h2, h3⟩ := hout i
      refine ⟨h1, h2, fun Y => ?_⟩
      rw [h3 Y]
      constructor
      · rintro ⟨X, hXY, hv⟩; refine ⟨X, hXY, ?_⟩; rw [hSDiff k X] at hv; exact hv
      · rintro ⟨X, hXY, hv⟩; refine ⟨X, hXY, ?_⟩; rw [hSDiff k X]; exact hv
    exact PEqualNP.Outside.L_lib_1482.part3_verifierW_to_realizes h n g deadline width f hmono k e D out held he hposD hszD hleg' hbnd' hout'
