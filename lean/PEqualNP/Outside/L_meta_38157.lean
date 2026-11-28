import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38157_aux

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def RunT {α : Type} (inv : α → α) (meet join : α → α → α) (tag : α → Bool)
    (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (save : Bool), tag a = false →
      P s (inv a :: kept save a r) → P (s + 1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      (c = true → tag a = false ∧ tag b = false) →
      (ka = true → tag a = false) → (kb = true → tag b = false) →
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws

section
variable {α : Type} {inv : α → α} {meet join : α → α → α} {tag : α → Bool} {y : α}

theorem RunT.done : RunT inv meet join tag y 0 [y] := fun _ d _ _ _ => d

theorem RunT.perm {s xs zs} (p : List.Perm xs zs) (h : RunT inv meet join tag y s xs) :
    RunT inv meet join tag y s zs := fun P d q u b => q p (h P d q u b)

theorem RunT.one {s a r} (save : Bool) (ht : tag a = false)
    (h : RunT inv meet join tag y s (inv a :: kept save a r)) :
    RunT inv meet join tag y (s + 1) (a :: r) := fun P d q u b => u save ht (h P d q u b)

theorem RunT.two {s a b r} (c ka kb : Bool)
    (hc : c = true → tag a = false ∧ tag b = false)
    (hta : ka = true → tag a = false) (htb : kb = true → tag b = false)
    (h : RunT inv meet join tag y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    RunT inv meet join tag y (s + 1) (a :: b :: r) := fun P d q u v => v c ka kb hc hta htb (h P d q u v)

theorem RunT.fold {P : ∀ t ws, RunT inv meet join tag y t ws → Prop}
    (done : P 0 [y] RunT.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunT inv meet join tag y s xs),
      P s xs h → P s zs (RunT.perm hp h))
    (one : ∀ {s a r} (save : Bool) (ht : tag a = false)
      (h : RunT inv meet join tag y s (inv a :: kept save a r)),
      P _ _ h → P _ _ (RunT.one save ht h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (hc : c = true → tag a = false ∧ tag b = false)
      (hta : ka = true → tag a = false) (htb : kb = true → tag b = false)
      (h : RunT inv meet join tag y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (RunT.two c ka kb hc hta htb h))
    {t ws} (h : RunT inv meet join tag y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : RunT inv meet join tag y s xs, P s xs h')
    ⟨RunT.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨RunT.perm hp h', perm hp h' ih⟩)
    (fun k ht ⟨h', ih⟩ => ⟨RunT.one k ht h', one k ht h' ih⟩)
    (fun c a b hc hta htb ⟨h', ih⟩ => ⟨RunT.two c a b hc hta htb h', two c a b hc hta htb h' ih⟩)
  exact hex.elim fun _ hp => hp

end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem RunT.map {α β : Type} (e : α → β)
    {inv : α → α} {meet join : α → α → α} {tag : α → Bool}
    {inv' : β → β} {meet' join' : β → β → β} {tag' : β → Bool}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    (htag : ∀ a, tag' (e a) = tag a)
    {y : α} {s : ℕ} {ws : List α} (h : RunT inv meet join tag y s ws) :
    RunT inv' meet' join' tag' (e y) s (ws.map e) := by
  induction h using RunT.fold with
  | done => exact RunT.done
  | perm hp _ ih => exact RunT.perm (hp.map e) ih
  | @one s a rest save ht _ ih =>
    have e1 : (inv a :: kept save a rest).map e
        = inv' (e a) :: kept save (e a) (rest.map e) := by
      simp [kept_map, hi]
    rw [e1] at ih
    exact RunT.one save ((htag a).trans ht) ih
  | @two s a b rest conj ka kb hc hta htb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact RunT.two conj ka kb
      (fun h => ⟨(htag a).trans (hc h).1, (htag b).trans (hc h).2⟩)
      (fun h => (htag a).trans (hta h)) (fun h => (htag b).trans (htb h)) ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

theorem length_wiresFrom (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    rw [wiresFrom_cons, ih]
    simp
    omega

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      rw [wiresFrom_cons, ht, List.append_assoc]⟩

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := wiresFrom_prefix gs w
  rw [ht]
  exact List.getD_append _ _ _ _ h

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem split_at (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hgp : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp [hlt.le]⟩
  calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
    _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hlt]
    _ = gs.take p ++ g :: gs.drop (p + 1) := by rw [hgp]

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def SCleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ j ≠ k ∧ g.inputs = [j, k])

theorem SCleanGate.lt {m : ℕ} {g : Gate} (h : SCleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, _, hin⟩ <;> rw [hin] <;> simp_all

def SCleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → SCleanGate (n + p) g

def statVal (w : List Bool) : Sum Bool ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Sum Bool ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Sum Bool ℕ, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Sum Bool ℕ, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def simpNot (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Sum Bool ℕ) → Option Gate × Sum Bool ℕ
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, if c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ)) : Option Gate × Sum Bool ℕ :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, SCleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpAnd] at hg
    · cases a <;> simp [simpAnd] at hg
    · cases a <;> cases b <;> simp only [simpAnd, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inl rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpAnd] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp [simpOr] at hg
    · cases a <;> simp [simpOr] at hg
    · cases a <;> cases b <;> simp only [simpOr, Option.mem_def] at hg
      all_goals try contradiction
      rename_i j k
      by_cases hjk : j = k
      · simp [hjk] at hg
      · simp only [hjk, ite_false, Option.some.injEq] at hg
        subst hg
        exact Or.inr ⟨Or.inr rfl, j, k, hv (Sum.inr j) (by simp), hv (Sum.inr k) (by simp), hjk, rfl⟩
    · simp [simpOr] at hg
  · rcases ins with _ | ⟨a, l⟩
    · simp [simpNot] at hg
    · cases a <;> simp only [simpNot, Option.mem_def] at hg
      · contradiction
      · rename_i j
        cases hg
        exact Or.inl ⟨rfl, j, hv (Sum.inr j) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Sum Bool ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b
      · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
      · rename_i c j; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j c; cases c <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      · rename_i j k
        by_cases hjk : j = k
        · subst hjk
          simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        · simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

theorem simplify_none_of_inl (op : GateOp) (m : ℕ) (ins : List (Sum Bool ℕ))
    (hlen : ins.length ≤ 2) (hnot : op = GateOp.not → ins.length ≤ 1)
    (h : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := h
  cases op <;> simp only [simplify]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · cases a <;> simp [simpAnd]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · cases b <;> simp [simpAnd]
      · cases a <;> simp [simpAnd]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hc
    · cases a <;> simp [simpOr]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · cases b <;> simp [simpOr]
      · cases a <;> simp [simpOr]
    · simp at hlen
  · have hl1 := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp [simpNot]
    · simp at hl1

def simpStep (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    List (Sum Bool ℕ) × List Gate :=
  let r := simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def simpPass (n : ℕ) (gs : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    List (Sum Bool ℕ) × List Gate :=
  gs.foldl (simpStep n) acc

theorem simpStep_len_le (n : ℕ) (acc : List (Sum Bool ℕ) × List Gate) (g : Gate) :
    (simpStep n acc g).2.length ≤ acc.2.length + 1 := by
  simp only [simpStep, List.length_append]
  cases (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp

theorem simpPass_len (n : ℕ) (gs : List Gate) : ∀ acc : List (Sum Bool ℕ) × List Gate,
    (simpPass n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep n acc g)
    have h2 := simpStep_len_le n acc g
    have h3 : simpPass n (g :: gs) acc = simpPass n gs (simpStep n acc g) := rfl
    rw [h3, List.length_cons]
    omega

theorem simpPass_len_drop (m v : ℕ) (b : Bool) (gs : List Gate) :
    ∀ acc : List (Sum Bool ℕ) × List Gate,
      (∀ g ∈ gs, g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) →
      v < acc.1.length →
      acc.1.getD v (Sum.inl false) = Sum.inl b →
      (simpPass m gs acc).2.length + (gs.countP (fun g => decide (v ∈ g.inputs)))
        ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [simpPass]
  | cons g gs ih =>
    intro acc hok hvl hvb
    have hstep_v : v < (simpStep m acc g).1.length := by simp [simpStep]; omega
    have hstep_b : (simpStep m acc g).1.getD v (Sum.inl false) = Sum.inl b := by
      simp only [simpStep]
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact hvb
    have ih' := ih (simpStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hstep_v hstep_b
    have h3 : simpPass m (g :: gs) acc = simpPass m gs (simpStep m acc g) := rfl
    rw [h3, List.countP_cons, List.length_cons]
    by_cases hv : v ∈ g.inputs
    · have hnone : (simplify g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        have hg := hok g List.mem_cons_self
        apply simplify_none_of_inl _ _ _ (by simpa using hg.1) (fun hop => by simpa using hg.2 hop)
        exact ⟨b, List.mem_map.2 ⟨v, hv, hvb⟩⟩
      have hlen0 : (simpStep m acc g).2.length = acc.2.length := by
        simp only [simpStep, hnone, Option.toList_none, List.append_nil]
      simp only [hv, decide_true, ite_true]
      omega
    · have hlen1 := simpStep_len_le m acc g
      simp only [hv, decide_false, Bool.false_eq_true, ite_false]
      omega

def SimpInv (n : ℕ) (x : List Bool) (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧
  SCleanL n acc.2 ∧
  ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 x) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem simpPass_inv (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List (Sum Bool ℕ) × List Gate),
      (∀ g ∈ gs,
        (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      SimpInv n x w acc →
      SimpInv n x (wiresFrom gs w) (simpPass n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (simpStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hcl, hi⟩ := h
    set w' := wiresFrom acc.2 x with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hx]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hvins : ∀ s ∈ ins, statValid (n + acc.2.length) s := by
      intro s hs
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
      exact (hi a).1
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by rw [lw']; exact hvins)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) x = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht⟩ := wiresFrom_prefix r.1.toList w'
    have hcl' : SCleanL n (acc.2 ++ r.1.toList) := by
      intro p g' hpg'
      cases hr1 : r.1 with
      | none =>
        rw [hr1] at hpg'
        simp only [Option.toList_none, List.append_nil] at hpg'
        exact hcl p g' hpg'
      | some g0 =>
        rw [hr1] at hpg'
        simp only [Option.toList_some] at hpg'
        by_cases hp : p < acc.2.length
        · rw [List.getElem?_append_left hp] at hpg'
          exact hcl p g' hpg'
        · have hpe : p = acc.2.length := by
            have := (List.getElem?_eq_some_iff.1 hpg').1
            simp at this
            omega
          subst hpe
          rw [List.getElem?_append_right le_rfl] at hpg'
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hpg'
          subst hpg'
          exact simplify_clean g.op (n + acc.2.length) ins hvins g0 (by simp [← hr, hr1])
    refine ⟨by simp [simpStep, hl], hcl', ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) x) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_len _ _ _ _ rfl, hl, getD_snoc_len _ _ _ _ rfl]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem exists_sclean {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ gs o, gs.length ≤ s ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  have hok : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    rcases hop with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  set init : List (Sum Bool ℕ) := List.ofFn fun i : Fin n => Sum.inr i.val
  set acc := simpPass n C.gates (init, [])
  have hinit : ∀ x : Fin n → Bool, SimpInv n (List.ofFn x) (List.ofFn x) (init, []) := by
    intro x
    refine ⟨by simp [init], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp [init, hi, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by simp [init]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ x : Fin n → Bool,
      SimpInv n (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := fun x =>
    simpPass_inv n (List.ofFn x) (by simp) C.gates (List.ofFn x) (init, []) hok (hinit x)
  have hlen : acc.2.length ≤ s := by
    have := simpPass_len n C.gates (init, [])
    simp only [List.length_nil, zero_add] at this
    exact le_trans this hsz
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have h1 := ((hinv y).2.2 C.output).2
    have h2 := ((hinv y').2.2 C.output).2
    rw [hst] at h1 h2
    have e1 : wiresFrom C.gates (List.ofFn y) = C.wires (List.ofFn y) := rfl
    have e2 : wiresFrom C.gates (List.ofFn y') = C.wires (List.ofFn y') := rfl
    rw [← hev y, ← hev y']
    show (C.wires (List.ofFn y)).getD C.output false = (C.wires (List.ofFn y')).getD C.output false
    rw [← e1, ← e2, ← h1, ← h2]
    rfl
  | inr o =>
    obtain ⟨y, _, _⟩ := hnc
    have ho : o < n + acc.2.length := by
      have hv := ((hinv y).2.2 C.output).1
      rw [hst] at hv
      exact hv
    refine ⟨acc.2, o, hlen, (hinv y).2.1, ho, ?_⟩
    intro x
    have hv := ((hinv x).2.2 C.output).2
    rw [hst] at hv
    have e1 : wiresFrom C.gates (List.ofFn x) = C.wires (List.ofFn x) := rfl
    rw [← hev x]
    show (wiresFrom acc.2 (List.ofFn x)).getD o false = (C.wires (List.ofFn x)).getD C.output false
    rw [← e1, ← hv]
    rfl

def substIn {n m : ℕ} (c : Fin n → Sum Bool (Fin m)) (x : Fin m → Bool) : Fin n → Bool :=
  fun i => match c i with
    | Sum.inl b => b
    | Sum.inr j => x j

def initSubst {n m : ℕ} (c : Fin n → Sum Bool (Fin m)) : List (Sum Bool ℕ) :=
  List.ofFn fun i : Fin n => match c i with
    | Sum.inl b => Sum.inl b
    | Sum.inr j => Sum.inr j.val

theorem sclean_fanInTwo {m : ℕ} {gs : List Gate} (hcl : SCleanL m gs) (o : ℕ) :
    FanInTwo ⟨gs, o⟩ := by
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
  have hcg := hcl p gs[p] (List.getElem?_eq_getElem hp)
  rcases hcg with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, _, hin⟩
  · exact ⟨by simp [hop], by simp [hin]⟩
  · rcases hop with hop | hop <;> exact ⟨by simp [hop], by simp [hin]⟩

theorem restrict_sclean_drop {n m : ℕ} (f : BFn n) (c : Fin n → Sum Bool (Fin m))
    (v : Fin n) (hv : c v = Sum.inl false)
    (hnc_sub : ∃ y y' : Fin m → Bool, f (substIn c y) ≠ f (substIn c y'))
    (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hev : ∀ x, val gs n o x = f x) :
    HasCircuitSize m (fun y => f (substIn c y))
      (gs.length - gs.countP (fun g => decide (v.val ∈ g.inputs))) := by
  have hok_inv : ∀ g ∈ gs,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
    rcases hcl p gs[p] (List.getElem?_eq_getElem hp) with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, _, hin⟩
    · exact ⟨Or.inr (Or.inr hop), by simp [hin]⟩
    · rcases hop with hop | hop
      · exact ⟨Or.inl hop, by simp [hin]⟩
      · exact ⟨Or.inr (Or.inl hop), by simp [hin]⟩
  have hok_drop : ∀ g ∈ gs, g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1) := by
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hg
    rcases hcl p gs[p] (List.getElem?_eq_getElem hp) with ⟨hop, j, _, hin⟩ | ⟨hop, j, k, _, _, _, hin⟩
    · exact ⟨by simp [hin], fun _ => by simp [hin]⟩
    · rcases hop with hop | hop <;> exact ⟨by simp [hin], by simp [hop]⟩
  set init := initSubst c
  set acc := simpPass m gs (init, [])
  have hinit : ∀ y : Fin m → Bool, SimpInv m (List.ofFn y) (List.ofFn (substIn c y)) (init, []) := by
    intro y
    refine ⟨by simp [init, initSubst], by intro p g hg; simp at hg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp only [init, initSubst, substIn, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, hi, dite_true, Option.getD_some, wiresFrom, List.foldl_nil]
      cases hc : c ⟨i, hi⟩ with
      | inl b => simp [statValid, statVal]
      | inr j => simp [statValid, statVal, j.isLt]
    · rw [List.getD_eq_default _ _ (by simp [init, initSubst]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ y : Fin m → Bool,
      SimpInv m (List.ofFn y) (wiresFrom gs (List.ofFn (substIn c y))) acc := fun y =>
    simpPass_inv m (List.ofFn y) (by simp) gs (List.ofFn (substIn c y)) (init, []) hok_inv (hinit y)
  have hv_init : init.getD v.val (Sum.inl false) = Sum.inl false := by
    simp [init, initSubst, v.isLt, hv]
  have hlen_drop := simpPass_len_drop m v.val false gs (init, []) hok_drop
    (by simp [init, initSubst, v.isLt]) hv_init
  simp only [List.length_nil, zero_add] at hlen_drop
  change acc.2.length + gs.countP (fun g => decide (v.val ∈ g.inputs)) ≤ gs.length at hlen_drop
  cases hst : acc.1.getD o (Sum.inl false) with
  | inl c0 =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc_sub
    apply hne
    have h1 := ((hinv y).2.2 o).2
    have h2 := ((hinv y').2.2 o).2
    rw [hst] at h1 h2
    rw [← hev (substIn c y), ← hev (substIn c y')]
    unfold val
    rw [← h1, ← h2]
    rfl
  | inr o' =>
    obtain ⟨y0, _, _⟩ := hnc_sub
    refine ⟨⟨acc.2, o'⟩, sclean_fanInTwo (hinv y0).2.1 o', ?_, ?_⟩
    · show acc.2.length ≤ gs.length - gs.countP (fun g => decide (v.val ∈ g.inputs))
      omega
    · intro y
      have h1 := ((hinv y).2.2 o).2
      rw [hst] at h1
      dsimp only
      rw [← hev (substIn c y)]
      exact h1

theorem simpPass_acc1_len (m : ℕ) (gs : List Gate) :
    ∀ acc : List (Sum Bool ℕ) × List Gate,
      (simpPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [simpPass]
  | cons g gs ih =>
    intro acc
    have h1 := ih (simpStep m acc g)
    have h2 : (simpStep m acc g).1.length = acc.1.length + 1 := by simp [simpStep]
    have h3 : simpPass m (g :: gs) acc = simpPass m gs (simpStep m acc g) := rfl
    rw [h3, h1, h2, List.length_cons]
    omega

theorem simpPass_acc1_getD (m : ℕ) (gs : List Gate) (i : ℕ) :
    ∀ acc : List (Sum Bool ℕ) × List Gate, i < acc.1.length →
      (simpPass m gs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false) := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hi
    have hstep : i < (simpStep m acc g).1.length := by simp [simpStep]; omega
    have h3 : simpPass m (g :: gs) acc = simpPass m gs (simpStep m acc g) := rfl
    rw [h3, ih (simpStep m acc g) hstep]
    simp only [simpStep]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem simpPass_append (m : ℕ) (gs₁ gs₂ : List Gate) (acc : List (Sum Bool ℕ) × List Gate) :
    simpPass m (gs₁ ++ gs₂) acc = simpPass m gs₂ (simpPass m gs₁ acc) :=
  List.foldl_append

theorem restrict_sclean_drop2 {n m : ℕ} (f : BFn n) (c : Fin n → Sum Bool (Fin m))
    (v : Fin n) (hv : c v = Sum.inl false)
    (hnc_sub : ∃ y y' : Fin m → Bool, f (substIn c y) ≠ f (substIn c y'))
    (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (hev : ∀ x, val gs n o x = f x)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g)
    (hvin : v.val ∈ g.inputs) (hop : g.op = GateOp.not ∨ g.op = GateOp.and) :
    HasCircuitSize m (fun y => f (substIn c y)) (gs.length - 2) := by
  have hok_inv : ∀ g' ∈ gs,
      (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 := by
    intro g' hg'
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hg'
    rcases hcl q gs[q] (List.getElem?_eq_getElem hq) with ⟨hop', j, _, hin⟩ | ⟨hop', j, k, _, _, _, hin⟩
    · exact ⟨Or.inr (Or.inr hop'), by simp [hin]⟩
    · rcases hop' with hop' | hop'
      · exact ⟨Or.inl hop', by simp [hin]⟩
      · exact ⟨Or.inr (Or.inl hop'), by simp [hin]⟩
  have hok_drop : ∀ g' ∈ gs, g'.inputs.length ≤ 2 ∧ (g'.op = GateOp.not → g'.inputs.length ≤ 1) := by
    intro g' hg'
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hg'
    rcases hcl q gs[q] (List.getElem?_eq_getElem hq) with ⟨hop', j, _, hin⟩ | ⟨hop', j, k, _, _, _, hin⟩
    · exact ⟨by simp [hin], fun _ => by simp [hin]⟩
    · rcases hop' with hop' | hop' <;> exact ⟨by simp [hin], by simp [hop']⟩
  obtain ⟨pre, post, hsplit, hplen⟩ := split_at gs p g hg
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  set init := initSubst c
  set acc1 := simpPass m pre (init, [])
  set acc2 := simpStep m acc1 g
  set acc := simpPass m post acc2
  have hacc_eq : acc = simpPass m gs (init, []) := by
    conv_rhs => rw [hsplit]
    rw [simpPass_append]
    rfl
  have hinit : ∀ y : Fin m → Bool, SimpInv m (List.ofFn y) (List.ofFn (substIn c y)) (init, []) := by
    intro y
    refine ⟨by simp [init, initSubst], by intro q g' hqg; simp at hqg, ?_⟩
    intro i
    by_cases hi : i < n
    · simp only [init, initSubst, substIn, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, hi, dite_true, Option.getD_some, wiresFrom, List.foldl_nil]
      cases hc : c ⟨i, hi⟩ with
      | inl b => simp [statValid, statVal]
      | inr j => simp [statValid, statVal, j.isLt]
    · rw [List.getD_eq_default _ _ (by simp [init, initSubst]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩
  have hinv : ∀ y : Fin m → Bool,
      SimpInv m (List.ofFn y) (wiresFrom gs (List.ofFn (substIn c y))) acc := by
    intro y; rw [hacc_eq]
    exact simpPass_inv m (List.ofFn y) (by simp) gs (List.ofFn (substIn c y)) (init, []) hok_inv (hinit y)
  have hl1 : acc1.1.length = n + p := by
    have h1 := simpPass_acc1_len m pre (init, [])
    change acc1.1.length = init.length + pre.length at h1
    simp only [init, initSubst, List.length_ofFn] at h1
    omega
  have hv1 : acc1.1.getD v.val (Sum.inl false) = Sum.inl false := by
    rw [simpPass_acc1_getD m pre v.val (init, []) (by simp [init, initSubst, v.isLt])]
    simp [init, initSubst, v.isLt, hv]
  have hcl_g := hcl p g hg
  have hg_res : (simplify g.op (m + acc1.2.length)
      (g.inputs.map fun i => acc1.1.getD i (Sum.inl false))).1 = none ∧
      ∃ b0 : Bool, (simplify g.op (m + acc1.2.length)
        (g.inputs.map fun i => acc1.1.getD i (Sum.inl false))).2 = Sum.inl b0 := by
    rcases hcl_g with ⟨hnot, j, _, hin⟩ | ⟨hor_and, j, k, _, _, _, hin⟩
    · rw [hin] at hvin
      have hjv : j = v.val := (List.mem_singleton.1 hvin).symm
      subst hjv
      rw [hnot, hin, List.map_cons, List.map_nil, hv1]
      exact ⟨rfl, true, rfl⟩
    · rcases hop with hnot | hand
      · rcases hor_and with h | h <;> rw [h] at hnot <;> cases hnot
      · rw [hin] at hvin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hvin
        rcases hvin with h | h
        · rw [hand, hin, List.map_cons, List.map_cons, List.map_nil, ← h, hv1]
          cases acc1.1.getD k (Sum.inl false) <;> simp [simplify, simpAnd]
        · rw [hand, hin, List.map_cons, List.map_cons, List.map_nil, ← h, hv1]
          cases acc1.1.getD j (Sum.inl false) <;> simp [simplify, simpAnd]
  obtain ⟨hnone_g, b0, hb0⟩ := hg_res
  have hacc2_len : acc2.2.length = acc1.2.length := by
    simp only [acc2, simpStep, hnone_g, Option.toList_none, List.append_nil]
  have hacc2_1_len : acc2.1.length = n + p + 1 := by simp [acc2, simpStep, hl1]
  have hacc2_np : acc2.1.getD (n + p) (Sum.inl false) = Sum.inl b0 := by
    simp only [acc2, simpStep]
    rw [getD_snoc_len _ _ _ _ hl1]
    exact hb0
  have hacc_np : acc.1.getD (n + p) (Sum.inl false) = Sum.inl b0 := by
    rw [simpPass_acc1_getD m post (n + p) acc2 (by omega)]
    exact hacc2_np
  have hne_o : n + p ≠ o := by
    intro ho_eq
    obtain ⟨y, y', hne⟩ := hnc_sub
    apply hne
    have h1 := ((hinv y).2.2 o).2
    have h2 := ((hinv y').2.2 o).2
    rw [← ho_eq, hacc_np] at h1 h2
    rw [← hev (substIn c y), ← hev (substIn c y')]
    unfold val
    rw [← ho_eq, ← h1, ← h2]
    rfl
  obtain ⟨q, g', hqg', hnp_in⟩ : ∃ (q : ℕ) (g' : Gate), gs[q]? = some g' ∧ n + p ∈ g'.inputs := by
    rcases hnd p hplt with h | h
    · exact absurd h hne_o
    · exact h
  have hq_gt : p < q := by
    have := (hcl q g' hqg').lt (n + p) hnp_in
    omega
  have hg'_post : g' ∈ post := by
    have hlt_q : q < gs.length := (List.getElem?_eq_some_iff.1 hqg').1
    have hq_sub : q - (p + 1) < post.length := by
      have : gs.length = pre.length + 1 + post.length := by rw [hsplit]; simp; omega
      omega
    have hget : post[q - (p + 1)] = g' := by
      have h1 : gs[q]? = post[q - (p + 1)]? := by
        conv_lhs => rw [hsplit]
        rw [List.getElem?_append_right (by omega)]
        have : q - pre.length = (q - (p + 1)) + 1 := by omega
        rw [this, List.getElem?_cons_succ]
      rw [hqg', List.getElem?_eq_getElem hq_sub] at h1
      exact Option.some.inj h1.symm
    rw [← hget]
    exact List.getElem_mem hq_sub
  have hpost_pos : 1 ≤ post.countP (fun g => decide (n + p ∈ g.inputs)) :=
    List.countP_pos_iff.2 ⟨g', hg'_post, by simp [hnp_in]⟩
  have hdrop_post := simpPass_len_drop m (n + p) b0 post acc2
    (fun g0 hg0 => hok_drop g0 (by rw [hsplit]; simp [hg0])) (by omega) hacc2_np
  change acc.2.length + post.countP (fun g => decide (n + p ∈ g.inputs)) ≤ acc2.2.length + post.length at hdrop_post
  have hpre_len := simpPass_len m pre (init, [])
  simp only [List.length_nil, zero_add] at hpre_len
  change acc1.2.length ≤ pre.length at hpre_len
  have htot_len : gs.length = p + 1 + post.length := by rw [hsplit]; simp [hplen]; omega
  cases hst : acc.1.getD o (Sum.inl false) with
  | inl c0 =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc_sub
    apply hne
    have h1 := ((hinv y).2.2 o).2
    have h2 := ((hinv y').2.2 o).2
    rw [hst] at h1 h2
    rw [← hev (substIn c y), ← hev (substIn c y')]
    unfold val
    rw [← h1, ← h2]
    rfl
  | inr o' =>
    obtain ⟨y0, _, _⟩ := hnc_sub
    refine ⟨⟨acc.2, o'⟩, sclean_fanInTwo (hinv y0).2.1 o', ?_, ?_⟩
    · show acc.2.length ≤ gs.length - 2
      omega
    · intro y
      have h1 := ((hinv y).2.2 o).2
      rw [hst] at h1
      dsimp only
      rw [← hev (substIn c y)]
      exact h1

theorem wiresFrom_indep (gs : List Gate) (v : ℕ) (hni : ∀ g ∈ gs, v ∉ g.inputs) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ a, a ≠ v → w₁.getD a false = w₂.getD a false) →
      ∀ a, a ≠ v → (wiresFrom gs w₁).getD a false = (wiresFrom gs w₂).getD a false := by
  induction gs with
  | nil => intro w₁ w₂ _ heq a ha; exact heq a ha
  | cons g gs ih =>
    intro w₁ w₂ hlen heq
    have hg : v ∉ g.inputs := hni g List.mem_cons_self
    have hmap : g.inputs.map (fun i => w₁.getD i false) = g.inputs.map (fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro a ha
      exact heq a (fun e => hg (e ▸ ha))
    set c := g.op.eval (g.inputs.map fun i => w₁.getD i false)
    rw [wiresFrom_cons, wiresFrom_cons, ← hmap]
    apply ih (fun g' hg' => hni g' (List.mem_cons_of_mem _ hg')) (w₁ ++ [c]) (w₂ ++ [c]) (by simp [hlen])
    intro a ha
    by_cases hal : a = w₁.length
    · subst hal
      rw [getD_snoc_len _ _ _ _ rfl, getD_snoc_len _ _ _ _ hlen.symm]
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact heq a ha

theorem countP_pos_of_dep {n : ℕ} (f : BFn n) (v : Fin n)
    (hdep : ∃ y : Fin n → Bool, f y ≠ f (Function.update y v (!y v)))
    (hnoproj : ∃ y : Fin n → Bool, f y ≠ y v)
    (gs : List Gate) (o : ℕ) (hev : ∀ x, val gs n o x = f x) :
    1 ≤ gs.countP (fun g => decide (v.val ∈ g.inputs)) := by
  by_contra! h0
  have hzero : gs.countP (fun g => decide (v.val ∈ g.inputs)) = 0 := by omega
  have hni : ∀ g ∈ gs, v.val ∉ g.inputs := by
    intro g hg
    have hfalse := (List.countP_eq_zero.1 hzero) g hg
    simpa using hfalse
  have hne_o : o ≠ v.val := by
    intro ho
    obtain ⟨y, hy⟩ := hnoproj
    apply hy
    rw [← hev y, ho, val_input]
  obtain ⟨y, hy⟩ := hdep
  apply hy
  rw [← hev y, ← hev (Function.update y v (!y v))]
  unfold val
  apply wiresFrom_indep gs v.val hni (List.ofFn y) (List.ofFn (Function.update y v (!y v))) (by simp)
  · intro a ha
    by_cases han : a < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, han, dite_true, Option.getD_some]
      have hne_fin : (⟨a, han⟩ : Fin n) ≠ v := fun e => ha (congrArg Fin.val e)
      simp [Function.update, hne_fin]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  · exact hne_o

theorem direct_f0_step {n m : ℕ} (f : BFn n) (c : Fin n → Sum Bool (Fin m))
    (v : Fin n) (hv : c v = Sum.inl false)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hnc_sub : ∃ y y' : Fin m → Bool, f (substIn c y) ≠ f (substIn c y'))
    (hdep : ∃ y : Fin n → Bool, f y ≠ f (Function.update y v (!y v)))
    (hnoproj : ∃ y : Fin n → Bool, f y ≠ y v)
    (cap : ℕ) (h : HasCircuitSize n f cap) :
    HasCircuitSize m (fun y => f (substIn c y)) (cap - 1) := by
  obtain ⟨gs, o, hlen, hcl, _, hev⟩ := exists_sclean f hnc cap h
  have hpos := countP_pos_of_dep f v hdep hnoproj gs o hev
  obtain ⟨C, hfan, hsz, hevC⟩ := restrict_sclean_drop f c v hv hnc_sub gs o hcl hev
  exact ⟨C, hfan, by omega, hevC⟩

def redir (m a : ℕ) : ℕ := if m < a then a - 1 else a

theorem redir_lt {m b a : ℕ} (hm : m ≤ b) (ha : a < b + 1) (hne : a ≠ m) : redir m a < b := by
  unfold redir
  split <;> omega

theorem redir_inj {m a b : ℕ} (ha : a ≠ m) (hb : b ≠ m) (heq : redir m a = redir m b) :
    a = b := by
  unfold redir at heq
  split at heq <;> split at heq <;> omega

theorem getD_drop_wire (w₁ u : List Bool) (b : Bool) (a : ℕ) (hne : a ≠ w₁.length) :
    (w₁ ++ u).getD (redir w₁.length a) false = (w₁ ++ [b] ++ u).getD a false := by
  unfold redir
  by_cases hlt : w₁.length < a
  · simp only [hlt, ite_true]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    have hlen : (w₁ ++ [b]).length = w₁.length + 1 := by simp
    rw [List.getElem?_append_right (by omega), hlen]
    congr 2
    omega
  · simp only [hlt, ite_false]
    have ha : a < w₁.length := by omega
    rw [List.getD_append _ _ _ _ ha]
    rw [List.append_assoc, List.getD_append _ _ _ _ ha]

theorem wiresFrom_drop_dead (w₁ : List Bool) (b : Bool) (post : List Gate) :
    ∀ u : List Bool,
      (∀ g ∈ post, w₁.length ∉ g.inputs) →
      ∃ u',
        wiresFrom (post.map fun g => ⟨g.op, g.inputs.map (redir w₁.length)⟩) (w₁ ++ u) = w₁ ++ u' ∧
        wiresFrom post (w₁ ++ [b] ++ u) = w₁ ++ [b] ++ u' := by
  induction post with
  | nil => intro u _; exact ⟨u, rfl, rfl⟩
  | cons g gs ih =>
    intro u hdead
    have hg : w₁.length ∉ g.inputs := hdead g List.mem_cons_self
    have hmap : (g.inputs.map (redir w₁.length)).map (fun i => (w₁ ++ u).getD i false)
        = g.inputs.map (fun i => (w₁ ++ [b] ++ u).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro a ha
      exact getD_drop_wire w₁ u b a (fun e => hg (e ▸ ha))
    set c := g.op.eval (g.inputs.map fun i => (w₁ ++ [b] ++ u).getD i false)
    obtain ⟨u', h1, h2⟩ := ih (u ++ [c]) (fun g' hg' => hdead g' (List.mem_cons_of_mem _ hg'))
    refine ⟨u', ?_, ?_⟩
    · simp only [List.map_cons, wiresFrom_cons, hmap]
      rw [List.append_assoc]
      exact h1
    · rw [wiresFrom_cons, List.append_assoc, List.append_assoc]
      rw [← List.append_assoc w₁ [b] (u ++ [c])]
      exact h2

theorem erase_dead (n : ℕ) (gs : List Gate) (o p : ℕ) (hcl : SCleanL n gs)
    (ho : o < n + gs.length) (hp : p < gs.length) (hne : n + p ≠ o)
    (hdead : ∀ (q : ℕ) (g : Gate), gs[q]? = some g → n + p ∉ g.inputs) :
    ∃ gs' o', gs'.length + 1 = gs.length ∧ SCleanL n gs' ∧ o' < n + gs'.length ∧
      ∀ x, val gs' n o' x = val gs n o x := by
  let gs' := gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩
  let o' := redir (n + p) o
  have hlen' : gs'.length + 1 = gs.length := by
    simp [gs']
    omega
  have ho' : o' < n + gs'.length := redir_lt (by omega) (by omega) (Ne.symm hne)
  have hcl' : SCleanL n gs' := by
    intro q g hqg
    by_cases hqp : q < p
    · have h1 : gs'[q]? = gs[q]? := by
        simp only [gs']
        rw [List.getElem?_append_left (by simp; omega)]
        exact List.getElem?_take_of_lt hqp
      rw [h1] at hqg
      exact hcl q g hqg
    · have hlt' : q < gs'.length := (List.getElem?_eq_some_iff.1 hqg).1
      have hq1 : q + 1 < gs.length := by omega
      have h1 : gs'[q]? = ((gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (redir (n + p))⟩)[q - p]? := by
        simp only [gs']
        rw [List.getElem?_append_right (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt hp)]
      rw [h1, List.getElem?_map, List.getElem?_drop] at hqg
      have hidx : p + 1 + (q - p) = q + 1 := by omega
      rw [hidx] at hqg
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hqg
      have hcl0 := hcl (q + 1) g0 hg0
      have hd0 := hdead (q + 1) g0 hg0
      rcases hcl0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hjk, hin⟩
      · refine Or.inl ⟨hop, redir (n + p) j, ?_, by simp [hin]⟩
        exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
      · refine Or.inr ⟨hop, redir (n + p) j, redir (n + p) k, ?_, ?_, ?_, by simp [hin]⟩
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · exact redir_lt (by omega) (by omega) (fun e => hd0 (by rw [hin]; simp [e]))
        · intro heq
          exact hjk (redir_inj (fun e => hd0 (by rw [hin]; simp [e]))
            (fun e => hd0 (by rw [hin]; simp [e])) heq)
  refine ⟨gs', o', hlen', hcl', ho', ?_⟩
  intro x
  unfold val
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    calc gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
      _ = gs.take p ++ gs[p] :: gs.drop (p + 1) := by rw [List.drop_eq_getElem_cons hp]
  set w₁ := wiresFrom (gs.take p) (List.ofFn x)
  have lw₁ : w₁.length = n + p := by
    rw [length_wiresFrom]
    simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hdead_post : ∀ g ∈ gs.drop (p + 1), w₁.length ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop] at hgk
    rw [lw₁]
    have hlt_k : p + 1 + k < gs.length := by simp at hk; omega
    exact hdead (p + 1 + k) g (by rw [List.getElem?_eq_getElem hlt_k, hgk])
  set b := gs[p].op.eval (gs[p].inputs.map fun i => w₁.getD i false)
  obtain ⟨u', hu1, hu2⟩ := wiresFrom_drop_dead w₁ b (gs.drop (p + 1)) [] hdead_post
  have heq1 : wiresFrom gs' (List.ofFn x) = w₁ ++ u' := by
    simp only [gs', wiresFrom_append]
    rw [← lw₁]
    simpa [w₁] using hu1
  have heq2 : wiresFrom gs (List.ofFn x) = w₁ ++ [b] ++ u' := by
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_cons]
    simpa [w₁, b] using hu2
  rw [heq1, heq2]
  show (w₁ ++ u').getD (redir (n + p) o) false = (w₁ ++ [b] ++ u').getD o false
  rw [← lw₁]
  exact getD_drop_wire w₁ u' b o (by rw [lw₁]; exact Ne.symm hne)

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

abbrev invFT {n : ℕ} : BFn n × Bool → BFn n × Bool := fun p => (invF p.1, false)
abbrev meetFT {n : ℕ} : BFn n × Bool → BFn n × Bool → BFn n × Bool := fun p q => (meetF p.1 q.1, false)
abbrev joinFT {n : ℕ} : BFn n × Bool → BFn n × Bool → BFn n × Bool := fun p q => (joinF p.1 q.1, false)

theorem countP_le_one_not_live (gs : List Gate) (o p a : ℕ) (g : Gate)
    (hg : gs[p]? = some g) (ha : a ∈ g.inputs) (hne : a ≠ o)
    (hc : gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1) :
    ¬ Live gs o (p + 1) a := by
  intro hl
  rcases hl with rfl | ⟨q, hq, g', hg', ha'⟩
  · exact hne rfl
  · obtain ⟨pre, post, hsplit, hplen⟩ := split_at gs p g hg
    have hq_post : g' ∈ post := by
      have hlt : q < gs.length := (List.getElem?_eq_some_iff.1 hg').1
      have hge : gs[q] = g' := (List.getElem?_eq_some_iff.1 hg').2
      have hq' : q - (p + 1) < post.length := by
        have hlen : gs.length = pre.length + 1 + post.length := by rw [hsplit]; simp; omega
        omega
      have hget : post[q - (p + 1)] = g' := by
        have h1 : gs[q]? = post[q - (p + 1)]? := by
          conv_lhs => rw [hsplit]
          rw [List.getElem?_append_right (by omega)]
          have : q - pre.length = (q - (p + 1)) + 1 := by omega
          rw [this, List.getElem?_cons_succ]
        rw [hg', List.getElem?_eq_getElem hq'] at h1
        exact Option.some.inj h1.symm
      rw [← hget]
      exact List.getElem_mem hq'
    have hpos : 0 < post.countP (fun g => decide (a ∈ g.inputs)) :=
      List.countP_pos_iff.2 ⟨g', hq_post, by simp [ha']⟩
    rw [hsplit, List.countP_append, List.countP_cons] at hc
    simp only [ha, decide_true, ite_true] at hc
    omega

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live_tagged (n : ℕ) (useTag : Bool) (gs : List Gate) (o : ℕ) (hcl : SCleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (tagged : ℕ → Bool)
    (htag : ∀ a, a < n → tagged a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or)) :
    let encW := fun a => (val gs n a, decide (a < n ∧ tagged a = true))
    ∀ d p, p + d = gs.length →
      RunT (invFT (n := n)) meetFT joinFT (fun p => useTag && p.2) (val gs n o, false) d
        ((liveList gs n o p).map encW) := by
  intro encW d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    have ho_tag : encW o = (val gs n o, false) := by
      simp only [encW, Prod.mk.injEq, true_and, decide_eq_false_iff_not, not_and]
      intro holt hto
      exact (htag o holt hto).1 rfl
    have hdone : RunT (invFT (n := n)) meetFT joinFT (fun p => useTag && p.2) (val gs n o, false) 0 ([o].map encW) := by
      simp only [List.map_cons, List.map_nil, ho_tag]
      exact RunT.done
    exact RunT.perm (hperm.map encW) hdone
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    have hguard : ∀ a ∈ g.inputs, decide (Live gs o (p + 1) a) = true → (useTag && (encW a).2) = false := by
      intro a ha hlive
      have h2 : (encW a).2 = false := by
        simp only [encW, decide_eq_false_iff_not, not_and]
        intro halt hta
        have ⟨hne, hc, _⟩ := htag a halt hta
        exact countP_le_one_not_live gs o p a g hg ha hne hc (of_decide_eq_true hlive)
      simp [h2]
    have hnot_or : ∀ a ∈ g.inputs, g.op ≠ GateOp.or → (useTag && (encW a).2) = false := by
      intro a ha hne_or
      have h2 : (encW a).2 = false := by
        simp only [encW, decide_eq_false_iff_not, not_and]
        intro halt hta
        exact hne_or ((htag a halt hta).2.2 p g hg ha)
      simp [h2]
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hjk, hinp⟩
    · have hjm := hin j (by simp [hinp])
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hjm
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hjm h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have hval : encW (n + p) = invFT (encW j) := by
        apply Prod.ext
        · funext x
          simp only [encW, invFT, invF]
          rw [hvg x, hop, hinp]
          simp [GateOp.eval]
        · simp [encW, invFT]
      have IH' := RunT.perm (hp2.map encW) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact RunT.perm (hp1.map encW).symm
        (RunT.one _ (hnot_or j (by simp [hinp]) (by simp [hop])) IH')
    · have hjm := hin j (by simp [hinp])
      have hkm := hin k (by simp [hinp])
      have hke : k ∈ (liveList gs n o p).erase j :=
        (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
      have hp1 : (liveList gs n o p).Perm
          (j :: k :: ((liveList gs n o p).erase j).erase k) :=
        (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
      have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
          a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
        intro a
        rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
            (kept (decide (Live gs o (p + 1) k)) k
              (((liveList gs n o p).erase j).erase k))) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
          · rw [mem_kept, mem_kept]
            rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
            · exact hnew j hjm h.symm
            · exact hnew k hkm h.symm
            · exact hnew _ ((hmr _).1 h).2.2 rfl
          · rw [hmr]; simp
          · rw [mem_kept, hmr]
            rintro (⟨_, h⟩ | h)
            · exact hjk h
            · exact h.2.1 rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
          simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
              · by_cases hak : a = k
                · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hjm, fun _ => h1⟩
            · exact Or.inr ⟨hkm, fun _ => h1⟩
            · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
      have IH' := RunT.perm (hp2.map encW) IH
      have hval : encW (n + p) = (if decide (g.op = GateOp.and)
          then meetFT (encW j) (encW k) else joinFT (encW j) (encW k)) := by
        rcases hop with hop | hop
        · simp only [hop, decide_true, ite_true]
          apply Prod.ext
          · funext x; simp only [encW, meetFT, meetF]; rw [hvg x, hop, hinp]; simp [GateOp.eval]
          · simp [encW, meetFT]
        · simp only [hop, decide_false, ite_false]
          apply Prod.ext
          · funext x; simp only [encW, joinFT, joinF]; rw [hvg x, hop, hinp]; simp [GateOp.eval]
          · simp [encW, joinFT]
      have hand_guard : decide (g.op = GateOp.and) = true → (useTag && (encW j).2) = false ∧ (useTag && (encW k).2) = false := by
        intro ha
        have hgop : g.op = GateOp.and := of_decide_eq_true ha
        exact ⟨hnot_or j (by simp [hinp]) (by simp [hgop]), hnot_or k (by simp [hinp]) (by simp [hgop])⟩
      rw [List.map_cons, kept_map, kept_map, hval] at IH'
      exact RunT.perm (hp1.map encW).symm
        (RunT.two _ _ _ hand_guard (hguard j (by simp [hinp])) (hguard k (by simp [hinp])) IH')

open Classical in
theorem exists_run_tagged {n : ℕ} (useTag : Bool) (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (tagged : ℕ → Bool)
    (htag_fn : ∀ (gs : List Gate) (o : ℕ), gs.length ≤ s → SCleanL n gs →
      (∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) →
      (∀ x, val gs n o x = f x) →
      ∀ a, a < n → tagged a = true →
        a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
        (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or))
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n × Bool),
      ws.Sublist (List.ofFn fun (i : Fin n) => ((fun x : Fin n → Bool => x i), tagged i.val)) ∧
      RunT (invFT (n := n)) meetFT joinFT (fun p => useTag && p.2) (f, false) s' ws := by
  have hex : ∃ m, ∃ gs o, gs.length = m ∧ SCleanL n gs ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact ⟨gs.length, gs, o, rfl, hcl, ho, hev⟩
  set m := Nat.find hex
  have hm_le : m ≤ s := by
    obtain ⟨gs, o, hl, hcl, ho, hev⟩ := exists_sclean f hnc s h
    exact le_trans (Nat.find_min' hex ⟨gs, o, rfl, hcl, ho, hev⟩) hl
  obtain ⟨gs, o, hlen, hcl, ho, hev⟩ := Nat.find_spec hex
  have hnd : ∀ p, p < gs.length → n + p = o ∨
      ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra! hbad
    obtain ⟨hne, hdead⟩ := hbad
    obtain ⟨gs', o', hlen', hcl', ho', hev'⟩ := erase_dead n gs o p hcl ho hp hne hdead
    have hlt : gs'.length < m := by omega
    exact Nat.find_min hex hlt ⟨gs', o', rfl, hcl', ho', fun x => (hev' x).trans (hev x)⟩
  let encW := fun a => (val gs n a, decide (a < n ∧ tagged a = true))
  refine ⟨gs.length, by omega, (liveList gs n o 0).map encW, ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => ((fun x : Fin n → Bool => x i), tagged i.val))
        = (List.range n).map encW := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, encW]
        have hi : i < n := by simpa using h1
        apply Prod.ext
        · exact (val_input gs n ⟨i, hi⟩).symm
        · simp [hi]
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live_tagged n useTag gs o hcl ho hnd tagged (htag_fn gs o (by omega) hcl hnd hev) gs.length 0 (by omega)

theorem runT_len {α inv meet join tag y s xs} (h : @RunT α inv meet join tag y s xs) :
    xs.length ≤ s + 1 := by
  induction h using RunT.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one save _ h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb _ _ _ h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

def lo (k : Nat) := 2 ^ k - 1
def mask (k : Nat) := lo (k + k)
def goal (k : Nat) := lo k <<< k

abbrev NatRunT (k : Nat) (useTag : Bool) :=
  RunT (fun w => (w &&& mask k) ^^^ mask k)
       (fun a b => (a &&& b) &&& mask k)
       (fun a b => (a ||| b) &&& mask k)
       (fun w => useTag && w.testBit (2 * k))

theorem mask_testBit_lt {k i : Nat} (hi : i < 2 * k) : (mask k).testBit i = true := by
  simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k + k by omega]

theorem mask_testBit_ge {k i : Nat} (hi : 2 * k ≤ i) : (mask k).testBit i = false := by
  simp [mask, lo, Nat.testBit_two_pow_sub_one, show ¬ i < k + k by omega]

theorem run_bits {k useTag y s xs} (h : NatRunT k useTag y s xs) (i j : Nat)
    (hi : i < 2 * k) (hj : j < 2 * k)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  have hmi := mask_testBit_lt hi
  have hmj := mask_testBit_lt hj
  induction h using RunT.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one save _ h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true, kept, List.mem_cons] at hmem
    · rcases hmem with rfl | hr
      · simp [ha, hmi, hmj]
      · exact hw _ (by simp [hr])
    · rcases hmem with rfl | rfl | hr
      · simp [ha, hmi, hmj]
      · exact ha
      · exact hw _ (by simp [hr])
  | two conj ka kb _ _ _ h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb, hmi, hmj] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k + i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all

theorem required {k useTag s ws} (h : NatRunT k useTag (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : (goal k).testBit i ≠ (goal k).testBit (k + i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k + i) (by omega) (by omega) hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def nextT (k : Nat) (useTag : Bool) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  let m := mask k
  let tk := 2 * k
  ws.any fun a =>
    let ra := ws.erase a
    let ta := useTag && a.testBit tk
    (slack ≥ 1 && !ta &&
      (let w := (a &&& m) ^^^ m
       f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        let tb := useTag && b.testBit tk
        [false, true].any fun conj =>
          !(conj && (ta || tb)) &&
          (let w := if conj then (a &&& b) &&& m else (a ||| b) &&& m
           f (w :: r) ||
             (slack ≥ 1 && ((!ta && f (w :: a :: r)) || (!tb && f (w :: b :: r)))) ||
             (slack ≥ 2 && !ta && !tb && f (w :: a :: b :: r))))

theorem nextT_one {k useTag a rest} {save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (ht : (useTag && a.testBit (2 * k)) = false)
    (h : NatRunT k useTag (goal k) s (((a &&& mask k) ^^^ mask k) :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRunT k useTag (goal k) s ys → f ys = true) :
    nextT k useTag (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := runT_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s + 2 - ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨by simp [hsl, ht], ?_⟩
  have hfn := hf _ (RunT.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at hfn; simp [hfn]
  | true =>
    simp [kept] at hfn hh
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [hfn, hsl2]

theorem nextT_two_sorted {k useTag a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (hc : conj = true → (useTag && a.testBit (2 * k)) = false ∧ (useTag && b.testBit (2 * k)) = false)
    (hta : ka = true → (useTag && a.testBit (2 * k)) = false)
    (htb : kb = true → (useTag && b.testBit (2 * k)) = false)
    (h : NatRunT k useTag (goal k) s
      ((if conj then (a &&& b) &&& mask k else (a ||| b) &&& mask k) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRunT k useTag (goal k) s ys → f ys = true) :
    nextT k useTag (s + 2 - ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := runT_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have hcg : !(conj && ((useTag && a.testBit (2 * k)) || (useTag && b.testBit (2 * k)))) = true := by
    cases conj
    · rfl
    · obtain ⟨h1, h2⟩ := hc rfl; simp [h1, h2]
  rw [Bool.and_eq_true]; refine ⟨hcg, ?_⟩
  have hfn := hf _ (RunT.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at hfn hh
  · simp [hfn]
  · have htbb := htb rfl
    have hsl1 : 1 ≤ s + 2 - ws.length := by omega
    simp [hfn, htbb, hsl1]
  · have htaa := hta rfl
    have hsl1 : 1 ≤ s + 2 - ws.length := by omega
    simp [hfn, htaa, hsl1]
  · have htaa := hta rfl
    have htbb := htb rfl
    have hsl2 : 2 ≤ s + 2 - ws.length := by omega
    simp [hfn, htaa, htbb, hsl2]

theorem nextT_two {k useTag a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (hc : conj = true → (useTag && a.testBit (2 * k)) = false ∧ (useTag && b.testBit (2 * k)) = false)
    (hta : ka = true → (useTag && a.testBit (2 * k)) = false)
    (htb : kb = true → (useTag && b.testBit (2 * k)) = false)
    (h : NatRunT k useTag (goal k) s
      ((if conj then (a &&& b) &&& mask k else (a ||| b) &&& mask k) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRunT k useTag (goal k) s ys → f ys = true) :
    nextT k useTag (s + 2 - ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact nextT_two_sorted hab p hc hta htb h f hf
  · apply nextT_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p)
      (fun h => (hc h).symm) htb hta _ f hf
    have he : (if conj then (a &&& b) &&& mask k else (a ||| b) &&& mask k)
        = (if conj then (b &&& a) &&& mask k else (b ||| a) &&& mask k) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply RunT.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_doneT {α inv meet join tag y t ws} (h : @RunT α inv meet join tag y t ws) :
    t = 0 → ws = [y] := by
  induction h using RunT.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem nextT_complete {k useTag t ws} (h : NatRunT k useTag (goal k) t ws) :
    ∀ s, t = s + 1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRunT k useTag (goal k) s ys → f ys = true) →
      nextT k useTag (s + 2 - zs.length) zs f = true := by
  induction h using RunT.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one save ht h ih => intro s he zs p f hf; cases he; exact nextT_one p ht h f hf
  | two conj ka kb hc hta htb h ih => intro s he zs p f hf; cases he; exact nextT_two p hc hta htb h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_testBit_ge {n : ℕ} (a : BFn n) (l : List ℕ) (j : ℕ) (hj : l.length ≤ j) :
    (encL a l).testBit j = false := by
  rw [encL_testBit, List.getD_eq_default _ _ (by simp; omega)]

def encT {n : ℕ} (l : List ℕ) (k : ℕ) (useTag : Bool) (p : BFn n × Bool) : Nat :=
  encL p.1 l ||| (if useTag && p.2 then 1 <<< (2 * k) else 0)

theorem encT_and_mask {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p : BFn n × Bool) :
    encT l k useTag p &&& mask k = encL p.1 l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encT, Nat.testBit_or]
  by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    cases hb : (useTag && p.2) <;> simp [hm, Nat.testBit_shiftLeft, show ¬ 2 * k ≤ j by omega]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    have he := encL_testBit_ge p.1 l j (by omega)
    simp [hm, he]

theorem encT_tag {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p : BFn n × Bool) :
    (useTag && (encT l k useTag p).testBit (2 * k)) = (useTag && p.2) := by
  rw [encT, Nat.testBit_or, encL_testBit_ge p.1 l (2 * k) (by omega), Bool.false_or]
  cases useTag <;> cases p.2 <;> simp [Nat.testBit_shiftLeft]

theorem encT_inv {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p : BFn n × Bool) :
    encT l k useTag (invFT p) = (encT l k useTag p &&& mask k) ^^^ mask k := by
  rw [encT_and_mask l k hl useTag p]
  simp only [encT, invFT, Bool.and_false, Bool.false_eq_true, ite_false, Nat.or_zero]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, encL_testBit, encL_testBit]
  by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    have hjl : j < l.length := by omega
    simp [hm, hjl, invF]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [hm]

theorem encT_and {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p q : BFn n × Bool) :
    encT l k useTag (meetFT p q) = (encT l k useTag p &&& encT l k useTag q) &&& mask k := by
  simp only [encT, meetFT, Bool.and_false, Bool.false_eq_true, ite_false, Nat.or_zero]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_or, Nat.testBit_or]
  by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    have hjl : j < l.length := by omega
    have hs : (1 <<< (2 * k)).testBit j = false := by
      simp [Nat.testBit_shiftLeft, show ¬ 2 * k ≤ j by omega]
    cases (useTag && p.2) <;> cases (useTag && q.2) <;>
      simp [hm, hs, encL_testBit, hjl, meetF]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    have he := encL_testBit_ge (meetF p.1 q.1) l j (by omega)
    simp [hm, he]

theorem encT_or {n : ℕ} (l : List ℕ) (k : ℕ) (hl : l.length = 2 * k)
    (useTag : Bool) (p q : BFn n × Bool) :
    encT l k useTag (joinFT p q) = (encT l k useTag p ||| encT l k useTag q) &&& mask k := by
  simp only [encT, joinFT, Bool.and_false, Bool.false_eq_true, ite_false, Nat.or_zero]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]
  by_cases hj : j < 2 * k
  · have hm := mask_testBit_lt hj
    have hjl : j < l.length := by omega
    have hs : (1 <<< (2 * k)).testBit j = false := by
      simp [Nat.testBit_shiftLeft, show ¬ 2 * k ≤ j by omega]
    cases (useTag && p.2) <;> cases (useTag && q.2) <;>
      simp [hm, hs, encL_testBit, hjl, joinF]
  · have hm := mask_testBit_ge (k := k) (i := j) (by omega)
    have he := encL_testBit_ge (joinF p.1 q.1) l j (by omega)
    simp [hm, he]

def moveBits (tag d w : Nat) : Nat :=
  ((w &&& tag) <<< d) ||| ((w >>> d) &&& tag) |||
    (w ^^^ ((w &&& tag) ||| (w &&& (tag <<< d))))

theorem moved (tag d i w : Nat) (h : (tag &&& (tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i) := by
  have ht := congrArg (fun v : Nat => v.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at ht
  simp only [moveBits, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind

theorem move_hom (tag d : Nat) (h : (tag &&& (tag <<< d)) = 0) (a b : Nat) :
    moveBits tag d (a &&& b) = (moveBits tag d a &&& moveBits tag d b) ∧
    moveBits tag d (a ||| b) = (moveBits tag d a ||| moveBits tag d b) ∧
    moveBits tag d (a ^^^ b) = (moveBits tag d a ^^^ moveBits tag d b) := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, moved tag d i _ h] <;>
    split_ifs <;> simp

theorem move_runT {k useTag s ws} (h : NatRunT k useTag (goal k) s ws) (tag d : Nat)
    (hz : (tag &&& (tag <<< d)) = 0) (hm : moveBits tag d (mask k) = mask k)
    (hy : moveBits tag d (goal k) = goal k)
    (ht1 : tag.testBit (2 * k) = false) (ht2 : (tag <<< d).testBit (2 * k) = false) :
    NatRunT k useTag (goal k) s (ws.map (moveBits tag d)) := by
  rw [← hy]
  exact RunT.map _
    (fun a => by rw [(move_hom tag d hz _ _).2.2, (move_hom tag d hz _ _).1, hm])
    (fun a b => by rw [(move_hom tag d hz _ _).1, (move_hom tag d hz _ _).1, hm])
    (fun a b => by rw [(move_hom tag d hz _ _).1, (move_hom tag d hz _ _).2.1, hm])
    (fun a => by rw [moved tag d (2 * k) a hz, ht1, ht2]; rfl)
    h

def applyMoves (ms : List (Nat × Nat)) (w : Nat) : Nat :=
  ms.foldl (fun acc p => moveBits p.1 p.2 acc) w

def moveOK (k : Nat) (p : Nat × Nat) : Bool :=
  (p.1 &&& (p.1 <<< p.2) == 0) &&
  (moveBits p.1 p.2 (mask k) == mask k) &&
  (moveBits p.1 p.2 (goal k) == goal k) &&
  (!p.1.testBit (2 * k)) &&
  (!(p.1 <<< p.2).testBit (2 * k))

theorem applyMoves_runT {k useTag s} (ms : List (Nat × Nat)) (hok : ms.all (moveOK k) = true) :
    ∀ ws, NatRunT k useTag (goal k) s ws →
      NatRunT k useTag (goal k) s (ws.map (applyMoves ms)) := by
  induction ms with
  | nil =>
    intro ws h
    have e : ws.map (applyMoves []) = ws := by
      have hfn : applyMoves [] = id := funext fun _ => rfl
      rw [hfn, List.map_id]
    rw [e]
    exact h
  | cons p ps ih =>
    intro ws h
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have hp := hok.1
    simp only [moveOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
    have h1 := move_runT h p.1 p.2 hp.1.1.1.1 hp.1.1.1.2 hp.1.1.2 hp.1.2 hp.2
    have h2 := ih hok.2 _ h1
    have e : ws.map (applyMoves (p :: ps)) = (ws.map (moveBits p.1 p.2)).map (applyMoves ps) := by
      rw [List.map_map]
      rfl
    rw [e]
    exact h2

theorem bits_le {k useTag y s ws} (h : NatRunT k useTag y s ws) (hl : ws.length = s + 1)
    (i j : Nat) (hi : i < 2 * k) (hj : j < 2 * k)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  have hmi := mask_testBit_lt hi
  have hmj := mask_testBit_lt hj
  induction h using RunT.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one save _ h ih =>
    have hh := runT_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := runT_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and, hmi, hmj] <;>
        grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k + i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k useTag s ws} (h : NatRunT k useTag (goal k) s ws) (hl : ws.length = s + 1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k + i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl (k + i) i (by omega) (by omega)
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k + i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s + 1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k useTag s ws} (h : NatRunT k useTag (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s + 1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {k useTag y s ws} (h : NatRunT k useTag y s ws) (hl : ws.length = s + 1)
    (v : Nat → Nat)
    (hand : ∀ a b, v ((a &&& b) &&& mask k) ≤ v a + v b)
    (hor : ∀ a b, v ((a ||| b) &&& mask k) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using RunT.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one save _ h ih =>
    have hh := runT_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb _ _ _ h ih =>
    have hh := runT_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {k useTag y s ws} (h : NatRunT k useTag y s ws) (hl : ws.length = s + 1)
    (a b c d e f : Nat)
    (ha : a < 2 * k) (hb : b < 2 * k) (hc : c < 2 * k)
    (hd : d < 2 * k) (he : e < 2 * k) (hf : f < 2 * k) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  have hma := mask_testBit_lt ha
  have hmb := mask_testBit_lt hb
  have hmc := mask_testBit_lt hc
  have hmd := mask_testBit_lt hd
  have hme := mask_testBit_lt he
  have hmf := mask_testBit_lt hf
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and, hma, hmb, hmc, hmd, hme, hmf, Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_and, Nat.testBit_or, hma, hmb, hmc, hmd, hme, hmf, Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def sumBelow (v : Nat → Nat) : List Nat → Nat → Bool
  | [], n => n != 0
  | w :: ws, n => decide (v w < n) && sumBelow v ws (n - v w)

theorem sumBelow_iff (v : Nat → Nat) (ws : List Nat) (n : Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n := by
  induction ws generalizing n with
  | nil => simp [sumBelow]
  | cons w ws ih =>
    rw [sumBelow, Bool.and_eq_true, decide_eq_true_eq, ih, List.map_cons, List.sum_cons]
    omega

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    let tk := 2 * k
    a < tk && b < tk && c < tk && d < tk && e < tk && f < tk &&
      ws.length == s + 1 && sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f (goal k))

theorem scoreCheck_no {k useTag s ws} (h : NatRunT k useTag (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hlt :
        (code &&& 1023) < 2 * k ∧ ((code >>> 10) &&& 1023) < 2 * k ∧
        ((code >>> 20) &&& 1023) < 2 * k ∧ ((code >>> 30) &&& 1023) < 2 * k ∧
        ((code >>> 40) &&& 1023) < 2 * k ∧ ((code >>> 50) &&& 1023) < 2 * k ∧
        ws.length = s + 1
    · obtain ⟨ha, hb, hc, hd, he, hf, hl⟩ := hlt
      simp only [ha, hb, hc, hd, he, hf, hl, decide_true, beq_self_eq_true, Bool.true_and]
      by_contra hbad
      have hsum := (sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
      exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      tauto

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem range_split {P : Nat → Prop} {lo mid hi : Nat}
    (h1 : ∀ i, lo ≤ i → i < mid → P i)
    (h2 : ∀ i, mid ≤ i → i < hi → P i) :
    ∀ i, lo ≤ i → i < hi → P i := fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo

def hw (seed w : Nat) : Nat :=
  let x := ((w &&& 4294967295) + ((w >>> 32) &&& 4294967295) * 3 +
            ((w >>> 64) &&& 4294967295) * 7 + ((w >>> 96) &&& 4294967295) * 11 +
            ((w >>> 128) &&& 4294967295) * 13 + ((w >>> 160) &&& 4294967295) * 17 +
            ((w >>> 192) &&& 4294967295) * 19 + ((w >>> 224) &&& 4294967295) * 23 +
            (w >>> 256) * 29 + seed) &&& 4294967295
  let y := ((x ^^^ (x >>> 16)) * 2246822519) &&& 4294967295
  ((y ^^^ (y >>> 13)) * 3266489917) &&& 4294967295

def hz (seed : Nat) : List Nat → Nat
  | [] => 0
  | w :: t => hw seed w + hz seed t

def hk (seed : Nat) (zs : List Nat) : Nat := hz seed zs &&& 4294967295

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} {useTag : Bool} (pool : List Nat) {zs : List Nat}
    (h : NatRunT k useTag (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (useTag : Bool) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → List Nat → Nat) (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(nextT k useTag (s + 2 - ws.length) ws fun zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k useTag S N idx ori pool} {s i : Nat}
    (hb : bar k useTag S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRunT k useTag (goal k) u ys → NatRunT k useTag (goal k) u (ori ys))
    (h : NatRunT k useTag (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRunT k useTag (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_doneT h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (zs) (hz : NatRunT k useTag (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (RunT.perm p (hr hz))
    have hN := nextT_complete h s rfl _ (List.Perm.refl _) F hF
    change !(nextT _ _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k useTag S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRunT k useTag (goal k) u ys → NatRunT k useTag (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k useTag S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRunT k useTag (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def pickMin (seed : Nat) (orig : List Nat) : List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [], best, _ => best
  | ms :: rest, best, bestH =>
    let img := orig.map (applyMoves ms)
    let h := hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH

theorem pickMin_runT {k useTag u} (seed : Nat) (orig : List Nat)
    (h0 : NatRunT k useTag (goal k) u orig) :
    ∀ (syms : List (List (Nat × Nat))) (best : List Nat) (bestH : Nat),
      syms.all (fun ms => ms.all (moveOK k)) = true →
      NatRunT k useTag (goal k) u best →
      NatRunT k useTag (goal k) u (pickMin seed orig syms best bestH)
  | [], _, _, _, hb => hb
  | ms :: rest, best, bestH, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    unfold pickMin
    dsimp only
    split
    · exact pickMin_runT seed orig h0 rest _ _ hok.2 (applyMoves_runT ms hok.1 orig h0)
    · exact pickMin_runT seed orig h0 rest best bestH hok.2 hb

namespace Main
abbrev fG : BFn 6 := fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 2 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 1 && x 5)

def taggedFn (_ : ℕ) : Bool := false

theorem htag_fn (gs : List Gate) (o : ℕ) (_ : gs.length ≤ 9) (_ : SCleanL 6 gs)
    (_ : ∀ p, p < gs.length → 6 + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ 6 + p ∈ g.inputs)
    (_ : ∀ x, val gs 6 o x = fG x) :
    ∀ a, a < 6 → taggedFn a = true →
      a ≠ o ∧ gs.countP (fun g => decide (a ∈ g.inputs)) ≤ 1 ∧
      (∀ (p : ℕ) (g : Gate), gs[p]? = some g → a ∈ g.inputs → g.op = GateOp.or) := by
  intro a _ h; simp [taggedFn] at h

def rowsG : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 4, 4, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 36, 36, 36, 36, 40, 40, 40, 40, 48, 48, 48, 48, 3, 5, 33, 3, 6, 34, 5, 6, 12, 20, 12, 24, 11, 13, 25, 41, 11, 14, 26, 42, 20, 24, 19, 21, 25, 49, 19, 22, 26, 50, 37, 38, 44, 52, 41, 42, 44, 56, 49, 50, 52, 56]

def xsG : List ℕ := [0x1111f07c13c0003c0f007, 0x222f13c42e4003c0f0038, 0x44f22489f4803c00003c0, 0x8f444bff4003c000ffc00, 0xf88ffd12803c03ff00000, 0xfff88220093ffc0000000]

theorem rowsG_len : rowsG.length = 84 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 6) => ((fun x : Fin 6 → Bool => x i), taggedFn i.val)).map
      (encT rowsG 42 false) = xsG := by decide +kernel

theorem enc_goalG : encT rowsG 42 false (fG, false) = goal 42 := by decide +kernel

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov 42 zs &&& lo 42) ≠ lo 42 := by decide +kernel

theorem no_subG (noRunFull : ∀ s ≤ 9, ¬ NatRunT 42 false (goal 42) s xsG) :
    ∀ s ≤ 9, ∀ zs : List ℕ, zs.Sublist xsG → NatRunT 42 false (goal 42) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

theorem mainG (noRunFull : ∀ s ≤ 9, ¬ NatRunT 42 false (goal 42) s xsG) :
    ¬ HasCircuitSize 6 fG 9 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ :=
    exists_run_tagged false fG ⟨pt 6 0, pt 6 3, by decide +kernel⟩ taggedFn htag_fn h
  have hr : NatRunT 42 false (encT rowsG 42 false (fG, false)) s'
      (ws.map (encT rowsG 42 false)) :=
    RunT.map (encT rowsG 42 false)
      (fun a => encT_inv rowsG 42 rowsG_len false a)
      (fun a b => encT_and rowsG 42 rowsG_len false a b)
      (fun a b => encT_or rowsG 42 rowsG_len false a b)
      (fun a => encT_tag rowsG 42 rowsG_len false a)
      hrun
  rw [enc_goalG] at hr
  refine no_subG noRunFull s' hs' _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _

def NN : Nat → Nat
  | 3 => 1
  | 4 => 10
  | 5 => 125
  | 6 => 456
  | 7 => 394
  | 8 => 26
  | 9 => 1
  | _ => 0

def HT : Nat → Nat → Nat
  | 3, 0 => 0x92475fae
  | 4, 0 => 0xf2449feddb5c4cd1c7b70944ab62764a8db9c6257b02956a7ae6e73c75d67dc2714d1f5c04eacdf2
  | 5, 0 => 0x4c66f3a5491327ee455f0b63450f511243627f4d4347c26d4317ac7442b37f4d4224724f4142ef8e3f002c803e526b143d9c32593c5deca2380e38f835c94b28358104b734b6cfab3239e87d30c685e92f2b51fe2eb913722e49cc262dff79ae2cf90bb42b9a3f20292019f7281b1a4826fa3bff22c30f1921a56d342153479320dfd1551bfaa8601b023da51953db2f18bcf456182c2eab1619dde8152926e2147397a113476d5e12d70a5311ff709711c654e810e996160eca30390cdf1ccd0cb03c710b8a7c270af526b908d8195e0865a8b707bd8c4707a1c2ca0741d33e070dc6ec068669b4059f798704fdf1f903ae7a7b02fc12d60232f4e60036f404
  | 5, 1 => 0xfb6c579ef88b506ee4c43231e421aad9e30b3d1ce0bc5b03d63aa66aceb1fc40ca648079ca6243fbc76ae67cc6da4697c68179f6c655b611c44c43edc417828dbc7cbd1bbbc2aa7cb2d3b049b14525faad0acdc3ac3c7f5ca8bc6e6da7c4a6a0a562410aa5119d14a162f8c49fdbee7e9f4a588397e02f94965c358490f5816e90c9bd898f500b198eabc8098e5cbcb58a70cb578a06b3b683f14de3836eb83e82cb2ce38263166a8229ef2380827e0d7ef7209b7e6df9b17a03abcf796cf67e7829c015765ea3e0744de91b721199186f57103a6c826996686dc51f63f7060f5ecad2dd58737f305167cc624e1203614de66411
  | 6, 0 => 0xe7ab88f0df0fabd0ddb0a710d7ce8ec0d2699a90d14d5720cab0ecf0c8260e90c678b280c1a02fa0b73de6a0b24b9b00af526b90ac6c1f10aa0c6bd0a5c04c109f52afc09ed14c909ebcb1508f71f2c089f7a6e0800829407ee4f7a07e1549f073cd5f806ec386f06d4a6ec06cb284b067da485066f9995065616d50653f42405df26ad05c02dcb05ac777a055d6c260516779404da3d5e04a7166b0463a6b4042f9104042a4ea303f8fc0603e448bc03d64b4603b75b2c03a96a65031caa7002b0b7330261309a0230d47601ee739901a94b94018c183e017edd46017a1fb1016885d4014f45cb0139873a01284b44010ddfda003d914600378e950036a9cf
  | 6, 1 => 0x20dd79dd20d02df920a8111720a1a6422096db3a20809790205163e220487c201fffc5d01f9d10761f54fd821f26ae7a1e477de21e1d7ce01dccfe001d9042f51d61356c1d1eb02a1cde2e3b1cb1cf201c9dc1981c13c06e1bdd09dc1adbe27e1adba34f1a9a81081a2ed0ca19a5e769195149371863a83518458a5d18278c3217ad527a17a77018177ad6921735cd1316ea689c16913a5a1645a3df15c80a171506bfe414eb5cfa14c9f8ef14c2270e133317c012febc1512d70a5312abb3831293aed5125471371227c6f011c5af0b1158c65011585224113afda510d6addf108139db105dba1b10373606101bae1c1005cef40f7cdcf00f4249700f0fe52d
  | 6, 2 => 0x37d636e8378f374b37663ef53742e797373e935536fe044e36305d81359f530a34aa66563483626e3440bea133d66a0833cfa1cb33cb875632ed52ca32e25cbf32532f8031fb9ae7319710bb3043d95b303629372fe860aa2f662f7c2ecbc23d2e67253a2d822d912d3c2bf62c6f19e82c6769582c2fc2632c1e32252bb3ef822b02fc922a7f14c62a73f3b72a3974262a1d85e12a16384829493a702898e59928892ef327675ee626ba201226a9c29e2687aaac265e8a3e25f96db125d6a920256f53e42519476e24c492f523f7c83f23d1cd0b239dbd91238775ea2373446723293c70232277af22f6b3ca22eee35522a8d96822a39b35219d4ca920ed870d
  | 6, 3 => 0x4e4f923b4defa0bd4d5f75874d5dbf2e4d48f0504c2778a14c24d4e84c055cf24bf257674bb188fb4baa611d4b9a37c14b5713454aef6e2f4a9321b349369990484a94ce48036071479a0ae4474aff90471fb1bb471e08d546ce85b546cb6d6346987f78459047b44546dd014529cbe84500a68a443c2c1443cb27e043aedb3f431941f043090d5842da20b94235ec0d41652fea412b551b411b77a740aeda2f40986534406fd101403754c83f6547b13f4ce06c3f44382a3e69759d3d5e00133d5ca07c3cd3184c3be90c463bbe60c53bb96fbe3bafda293b750eeb3afd802c3ae964ae3ab360473a6d9af53a67dd803955fd6838efb1c838e1afb63850f00e
  | 6, 4 => 0x6a0ef9af69ab51a76929a47b675c139a6733bea866b2265f65f2c5a264994d83636f22aa63284e9e62db3b496292738e6279c3c162414788619d12dc615de6846155ce4a613466bf613153d6609c8dbb604f78345fff8c035fda40135f9966755ee7b6a45ecad2dd5e6a516b5d98b5d25d1198405cd7f1bd5cc3e9435ab6f9fd5aa8c68f5a9e11d45a90051e5a513b9f5a508b7d5a3da796598b7d5a594fe78959073cd858ae703758a327535882ac52582ad1685819274956cc5f0c56c2cc525650873f55e05cc855a7a22355a23727555c7aad553c281c539ea143532027a95202b7f05140fe6a511d19c65022128f500073ce4fbcbe464fa3101d4e9c37dc
  | 6, 5 => 0x9db7a4749ba12a399b442fe099f70a5598afa50695d321c29263ea4591f53a4f90cab72990c9bd898ee345208dbf7b3a8d994ddf8d6f90268c66ad938c29d6538bdf68988a5755ff88fb562088a6f40885e2959585bc2ba48453866e8352c354835086d682d8942b82bbd74a82a6807b826f771d82596af482097ec37f0afaa97f008d447eeefe407ee1e47d7e3dafd17dff23a57d32ae197be9d33d7bdd09117bd956667bc23a077baaca0f7b918f3b7b724dd67946a8d277c4b7b07797c9ec775988ad770e9f7a76f1287276a5558e75f51a1174923a58741f536e729fa284729aecae7257d9f9721d62e7714d4a5f70a62a9c6db6b90a6c99e9136a3d12a9
  | 6, 6 => 0xe4c43231e3fae2a6e394c2a3e30c84d4de45ab9cde19f343ddb62c05dd813df6dd00b4c4d9eebf95d9d048e9d9a08deed53763d7d3f0f16dd3eabaadd1eba09bd12d22c1d0c8442fd0aa2ac9ceb1fc40ce42edafcdb60b13cc9c6692cc44e969cb57ceddca648079c86e7157c5e6afd5c574d75ac56f8e0fc51bd4c7c3d7f54dc2095afdbeef5b76beb356f5bdab1cf9bd79a0b7bcc072f5bc2abf77bc100083baf6c204b7e4ccd5b775f3a7b3c56aa5b1fcddd5b1e6feadb032d37ab005a1f8afca1c85af4f16d8af031eeeac6148bfaba8f18baa0e0861a91a1594a6c886daa58eadd2a4e2352aa0491d4f9f6f638e9f6ce9a29ec585279e56250f9de34926
  | 6, 7 => 0xfdfd93edfd5675eafcfc0c1ff8cf0648f54e896ef289ec90eb0ae2b2ea786417
  | 7, 0 => 0x144264ed13488c16123d26fe12300ac011c5af0b11ab29d1114e573910a4d2e90fe5eb170f8076040f77a8550efe968b0ef058ce0e8fe9a20dce6fd30dbb7fd70d9b4aec0d588b4c0d31c87d0d16a0560cd3d1330cc156f70cb5b35b0c85e1af0c1d7b780b112a930b0a6ed60ab2d9730a991ed50a6ce9f70a38e0d609d9f7120932500c0929fa370875b3d60800829407e8ebf407c96518071a15a106e7a15606c15a5f0675d920064805f605dc3c3e05c8ef4e05c477d205b81e2605b492e905977282055d6c2604b853cb04a989940484fbd70457d026042a4ea303b2726e034dc60b031f8b4402eae18d02033ec301f64b3c01ee73990196c2a700ec433e
  | 7, 1 => 0x2c2112f92b9041ae2b461cd42a1d85e12a04fcfd29b302342913b7d12845d56b27d2e20e27675ee626e9ad4d26c3587e2689919a2686ee8125f96db124e9ab1c24c492f5240d318323eb083e23d01a7723bab2962315090a230734d322f6b3ca22dd4cbd227de464210ef98a20d02df9206230931fee63001fec717b1fdd4ae21fa6df6e1f9c86671f6d039c1f23b7011f0f41561ecd83f61ec878d01e7d39e51dc9c8eb1dc45cf11d7600961cde2e3b1c9892691c408cb41b79a6131b5f814b1a39896119a5e769198400d818ea349f1863a83518425abe1713c43316acc625168e3803162e4044161b885a160102b61575991515605ce115097ad214b7abaa
  | 7, 2 => 0x4529cbe843c58458428ab6a7425fc9bb4232983941f855c041cf9e8541652fea4130152f40aeda2f40986534406fd101406cadad403754c83f44382a3e967dbd3e500e903e0b02873dd5e7cc3da6c28e3d3e37d13d15a39e3c8fb9453c350d7c3bea0ac73b9774553b8e31d33b4467d03b4136063a6d9af5399a7d733953643938db0e94389ab8323838330438001e403786986137136d9235feba8835f7a1c43528941c33d66a0833c9d07433c163e833b46128335849f9331cfb8d32c9c25032a25ff131c2288a30ec4d9d30ea73a930e91c1e307c3ca52fe9290b2fa53dac2f6544872f498dab2edecf242eddc3f32d86b2342d0d96492cf9bc8b2cc1190c
  | 7, 3 => 0x63d9914563d3e39b636f22aa62856346619d81e360973bfe604f78345fff8c035ef5aba45ec95cd35e4354805d628b7c5cf54ad15cd7f1bd5bf4def15b4db2235b25c49b5aeb834b5a314b1358ff55ff585b2c7d576ada425643e11655be53e85565e157544a69115436513e539ea1435372e0135337a7bc52da7a6952b489e952959a3451f8397c51f31bcb50e7b6b3504473e04fbdd5d24f5c0b254f2722fb4ec1649d4e9c37dc4e375e934dfba6584c8950474c3813484c0d612c4b5beade4b52e12e4b420a794a5085c64a17cb214a06afc148fdddd3487adea0486e8b51471fb1bb46ce85b546c59c9b45c4a55645bd90a645a7e30545882dfb4554f06e
  | 7, 4 => 0x9339ca899314fe1a929b4e9e924ba4da924667a390ce594990b903068f836c2b8f3f6b808e7066608def82f78d79401f8c29d6538b7dbbe88a5755ff8a3fe34089a9866c87256e5586ba6527855b826583ea16da8352c354815cb432808e3d687ee1e47d7e3dafd17e0d33477df825197df06ac27d37d8f37a99423b78df1c697748bd2976f128727627d8e775ab07e5755caa9274d5768174be7ca974bcd885744d108b729ece8b72067e4c71ff6588718bef9e70e3dacb6f9ab2d26f8e693f6ec9dc096e7d8ffa6d89ad686bfca81a6b35709d6b2422196a711651694a1d256907fd78689c879e6733bea8663de3cb651b7b9564bc173d6416fced63e4401a
  | 7, 5 => 0xe3d2497ee38d7fc2e30c84d4dfb25771dc42f91fd925780fd901b70ed773d342d34154b5d1f166f4d01e35cfcf418e4dcead9714ccb9039dc8bef6c9c86e7157c65bc999c61dd16ec5fb7affc5c9a562c5b14a30c34a479cc3088475c2b7b033c24d10d7bc100083baf6c204ba8bf80dba30a43ab93f2fd0b933e93ab8b5d320b7e4ccd5b76a031eb6b0cfbcb6a105ffb455979ab2c3d17bb1fcddd5b1e6feadb1495e40af46d4c8ae8cd14aad31bba1ac91efb1ac3548d4abeca765a785bbfea7240672a6740d97a64619a2a4e46ce2a4a44b62a366a6f29f41cbb39ccf76059cafc27b9ba12a3999b5b85b98aa9ac697ed240c9560105e952a395d9410710c
  | 7, 6 => 0xfc0784cbf7ac9d64f3a1a322f2d6002ff02d83b7ec07f31deb4e988ceb0ae2b2eabb94bae7bb3cf0
  | 8, 0 => 0xeb4e988ce38d7fc2c5b14a30924ba4da8f3f6b80815cb4327d37d8f371ff6588636f22aa5cd7f1bd52b489e941652fea38001e4033b461282fe9290b2eddc3f32c2112f924c492f523bab2961fee63001863a835162e404415097ad2114e5739055d6c2602033ec3
  | 9, 0 => 0x41652fea
  | _, _ => 0

def dictionaryBlocks : Nat → Nat → Nat
  | 0, 0 => 0x22489f4800000003c00002000000000000000000001705c12c0003c0f00700011044024000000000000011000000000000000000006c1bd080003f0ffc7000000cd76c00000fffff000000000000000000000
  | 0, 1 => 0x711c4264003c0f003800066d9bf48003fffffff00060d83e40003c3f0ff800055956024003ffffc3f000449df40000000ffc00000401000000000000000000334cdf6c003fffffff00033400b6c003ff003ff
  | 0, 2 => 0x177ddff6c003fffffff0011304c12c000000000000102008108000000000000077ddff6c003fffffff00077d56b6c003fffffff00077d12800003ff00000000771dc36c003fcff03f00075dd7e64003fffffff
  | 0, 3 => 0x20403c400000000f00000110607c108000000f0000100407c000000000f000010000200000000000000003220883480000000000003000003fc03c00003ff002200802400000000000002000000000000000000
  | 0, 4 => 0x45020895080000000000044000894000000000000044000000000000000000030443fc00000000ff000030002640b43c000ffc3f022603c424000000f0000022002c42e400000f0038020513c402400000f0000
  | 0, 5 => 0x77002ed7fc3fc00fffff077002ed7483fc00fffc0077002a97d83fc00fffff066002cd7ec3fc00fffff066002816c03fc00f0ff8054040fd400000000f0000470008974803c00003c0046200896400000000000
  | 0, 6 => 0x1101f07c0000003c0f0001101d0740340003c0f0071011b00013c0003c000071001f0100000003c0000007777fffffc3fffffffff07777f328903ffff00000077112ed7fc3fc00fffff077022ed7fc3fc00fffff
  | 0, 7 => 0x1111f07c13c0003c0f0071111f0300100003c000001111b06c13c0003c0f0071111b06c13c00000000001110e0381180003c0f0071110c07c010000000f0001110a0281180000000000111080200100000000000
  | 0, 8 => 0x1661f2916c03fc3cf0ff81551f0fd53c0003c0f0071315f3fc13c0003cff0071133f0fc37c0003c0f0071131f07c13c0003c0f0071117fdfff7c003fffffff11168da3e50003c3f0ff81115f17c13c0003c0f007
  | 0, 9 => 0x222a02802c00000000000222912440a40000000000222802000800000000000202b10002e4003c000038200f1144024003c000000200f1100000003c0000001771f2fd7fc3fc3cfffff177082ed7fc3fc00fffff
  | 0, 10 => 0x266f13cd6e4003c0f0038223f33cc3ec003c0f0038222f7fdffec003fffffff222f33c42e4003c0f0038222f13c42e4003c0f0038222e03802c0003c0f0038222d13c42e4003c0f0038222b12c42e40000000000
  | 0, 11 => 0x333aa2a83d800000000003339f27c1bc0003c0f007333992640b40000000000333882200900000000000330992640b7fc3ffffc3f3119f07c13c0003c0f007303990003ffc3fff003ff300990000b7c03ff0003f
  | 0, 12 => 0x408224008000000000000333fffffffc003fffffff333ff3fc3fc003fcff03f333fb3ec3fc003c0f0038333f93e42f4003c0f0038333ee3b83d8003fcff03f333bf2fc3fc0003c0f007333bb2ec3fc0000000000
  | 0, 13 => 0x44e20481e4003c00003c044d22489f4803c00003c044d02409d0803c00003c044c22489c000000000000438226648b43c000ffc3f40b22400b4803c00003c040922408908000000000040877ddff6c003fffffff
  | 0, 14 => 0x44f5595602403fffffc3f44f334cdf6c03c00003c044f26499f4803c00003c044f224cdf4803c00003c044f22489f4803c00003c044f2008024003c000000044f0008940003c000000044f0000000003c0000000
  | 0, 15 => 0x55f0802001003c000000051b3f4fcb7c0003c0f0075193f47c93c0003c0f00747f226edffc3fc00fffff46f627cdf4803c00f03c045f264fdf4803c000f3c045f224a9f4803c00003c044f77ddff6c03ffffffff
  | 1, 0 => 0x62af37c4ae4003c0f003862af13c42e4003c0f003860aa0400ac3c3fc3003f8608f3500800003c00000055f3f4fdf7c03c3c0f3c755f3b4edf7c03c00003c055f2a4a9f5803c00003c055f1f07c13c03c3c0f007
  | 1, 1 => 0x66ff13c42e403fc0f003866fb36cdfec03c00003c066fa2689fc803c00003c066ef37cdee4003c0f003866ea0681ec3fffc3f0ff866dd374ddac03fc0f03f864ff3589f4803fc0003c062bf37ccbec003c0f0038
  | 1, 2 => 0x73bbb664bffffffffffff71bbf47cbffc3fff0f3ff70bffddffffc3ffffffff70bbb400bffc3fff003ff70b88000093c3c00000007099b4009bfc3fff003ff708bb400803c03ff0000066ff37cdfec03fc0f03f8
  | 1, 3 => 0x77fff7fdffc03ffcff3ff77fbb6edfffffffffffff77fbb6edffc03c00003c077faa6a9fd803c00003c077f88220093ffc000000077f8822009003c000000077cbb6edc03fc3ffffc0074fbb489fffc3fff003ff
  | 1, 4 => 0x8c44499b40000000000008b044b760003c000ffc008a044bd600000000f0000883449123fc03c00003ff88077ddff6c003fffffff88055956027fc3ffffc3f880449120000000000000880000000000000000000
  | 1, 5 => 0x8f444bbb4003c000000008f444b7f4003c000ffc008f444b320003c000000008f433620b6c3c3ff003ff8f4002a94003c000000008f4002200003c000000008e444bdf4003c000ffc008d44493b4003c0000fc00
  | 1, 6 => 0x8f664bff6403c000ffc008f644bff4003c000ffc008f546bff5083c000ffc008f477ffff6c3c3fffffff8f464bff4003c000ffc008f455bff4243c000ffc008f444bff4b43c000ffc3f8f444bff4003c000ffc00
  | 1, 7 => 0x9f44cbff4003c000ffc009d55f9ff53c0003c0f0079915f97e13c0003c0f0079905d976037fc3ffffc3f9900c832013fc03f0fc078f766bff7483c000ffc008f744bff7fc3fc00fffff8f675bff6643c000ffc00
  | 1, 8 => 0xaa2f13c42e4003c0f0038aa1c2b0a18bfc3c3f0c38a80f5912000003c0000009f55fbff53c3c03cffc079f54ebff5183c000ffc009f54cbff4103c000ffc009f5082200103c000000009f45fbff4003c03cffc00
  | 1, 9 => 0xbb0aa6a9fdbfc000003c0bb088220093fc00000000b80dd912003c03ff00000af6f5bff6e43c3c0ffc38af6c4bff4803c000ffc00af6802200803c00000000ae6f5bdf6e4003c0f0038aa2f5bd62e4003c0f0038
  | 1, 10 => 0xbc7dd99b74bc3fff003c0bb2fdbf62f7fc3ffffc3fbb2ddb760b7fc3ffffc3fbb1dfb7e1bffc3ffffc3fbb188220093fc00000000bb0fffffffffc3fffffffbb0ddb760b7fc3ffffc3fbb0ccb32093fc3ffffc3f
  | 1, 11 => 0xccc11c47c27ffc0300fc0ccc00c03c03ffc0300fc0c8866d128000000000000bf7ddbff7ffffffffffffbf7ccbff4903c000ffc00bf7882200903c00000000bf4ddbff4b7fc3ffffc3fbf488220093fc00000000
  | 1, 12 => 0xcfe66fffe403c000ffc00cfd66fffd083c000ffc00cfc66fffc003c000ffc00ccf66d9bf4803c00003c0ccf22489f4803c00003c0ccc77ddff6fffffffffffccc66d9bc000000000000ccc60d83e43fffc3f0ff8
  | 1, 13 => 0xddd0ec3bd1bffc3f0ffc7ddd08020013ffc0000000ddc0cc33c13ffc3f0ffc7daa0eed6ae7c003ff0038d997fd7e93c0003c0f007d880ec12803c003f00000cff66ffff483fc00fffc0cff002200003fc0000000
  | 1, 14 => 0xe88f7d12800003c000000e88e4d12803c03c300000e88e0d02803c03c300000ddf2ecbbf5bffc3f0ffc7ddd7fdfff7fffffffffffddd4ed3bd1bffc3f0ffc7ddd1fc7fd3fffc3f0ffc7ddd0ecbbd1bffc3f0ffc7
  | 1, 15 => 0xeefe2f8bfcbfffc3f0ff8eeef7fdfee4003c0f0038eeef1fc7ee7fffc3f0ff8eeee0f83ec3fffc3f0ff8eee9725c1afffc3c0f007eecc0f03c83fffc3f0ff8eaaf7fd6ae4003c0f0038eaae0f02ac3fffc3f0ff8
  | 2, 0 => 0xf88ffd56803c03ff00000f88ffd12803c03ff00000f88eed12803c03ff00000f88eed12803c000000000f88aa400803c000000000f889f010003c003c00000f8888000003c000000000efff7ffffec3ffc0ffff8
  | 2, 1 => 0xf99ffd32813c03ff00000f8bffd12bffc3fff003fff8affd92a43c03ff00000f8affd12ae7c03ff00038f89ffd1a90bc03ff00000f89ffd1293fc03ff00007f88ffddff6fc03ffffffff88ffd56827c03ff00000
  | 2, 2 => 0xfb888220093fc00000000faafffd6ae7c03fff0038faafff92ac3c03ff00000faafff12883c03ff00000faaf93c42e7c03c0f0038f99ffd7e93fc03ff0f007f99ffd76837c03ff00000f99ffd3a91bc03ff00000
  | 2, 3 => 0xfcfaa489f4bc3c00003c0fccffd9bc03c03ff00000fccffd12803c03ff00000fbbffffebffc03ffff03ffbbfff76bfffffffffffffbbfff32893c03ff00000fbb88220093ffc0000000fb8fff768b7fc3ffffc3f
  | 2, 4 => 0xffcccbff403fc000ffc00ffc88220003fc00000000feffbf83fffffffff0ffffeefff93ec3ffffff0ff8fdfbfc3bffffffff0fffffddffd3bd1bfffff0ffc7fcfffd9bf4bc3fff003c0fcfffd12803c3fff00000
  | 2, 5 => 0xfff882ed7ffffc00ffffffff882a97dbffc00003c0fff882a9493ffc0000000fff88220093ffc0000000ffefffffee7fc3ffffc38ffefdff7ef7ffffffffffffe88220093ffc0000000ffcfffffc03fc3ffffc00
  | 2, 6 => 0xfff9b26c1bfffc0000000fff992640b7ffc0000000fff99220093ffc0000000fff8ee3bd9bffc3f0ffc7fff8a629d9bffc00003c0fff8a22819bffc0000000fff8a220093ffc0000000fff88e23c93ffc0300fc0
  | 2, 7 => 0xfffaa6a9c93ffc0000000fffaa6a0ad3ffc0000000fffaa620bdbffc00003c0fffaa620893ffc0000000fffaa2a83dbffc0000000fffa86a1ed3ffc00003c0fffa82a02d3ffc0000000fff9f27c1bfffc3c0f007
  | 2, 8 => 0xfffccbff493ffc00ffc00fffccb32093ffc0000000fffc8320093ffc0000000fffbf6fdfffffc3c0f3c7fffbb6edfffffc00003c0fffbb620bfffffff003fffffb92e42f7ffc0000000fffaa6a9fdbffc00003c0
  | 2, 9 => 0xffffb7edffffffc0f03f8ffff93e42f7fffc0f0038ffff9320093fffc000000fffeefbbfdbfffffffffffffeefbbfdbffc00003c0fffeef32893ffc0000000fffe8fa3ed3fffc3f0ff8fffddb760b7fffffffc3f
  | 2, 10 => 0xffffffffffffffffffffffffffffff4bffffffffc0ffffffffc93fffffffc00ffffffbbfdbfffff003c0ffffff7e9bffffff0f007ffffff32893fffff00000fffff3fc3ffffffcff03f
  | _, _ => 0

def stateBlocks : Nat → Nat → Nat → Nat
  | 3, 0, 0 => 0xa5bf87e3
  | 4, 0, 0 => 0x20cb03b17c92c7f3907e4832c13a6524196076301280e1298fc94b7094c7e4a0285183f24196073301258e4460fc94053a1c7e4
  | 5, 0, 0 => 0x4e16073318bca00a745160732f14012c90b94a63f28020cdb4e14c7e5004b1c86c298fca00a045960891f94012c90b84a63f280294f9581cc7e50050220b04194ca00a029cce531f94012c943f1c8532802810658240c2500419607632970a009641960903f1401468b330e63f280258b03b1945e5
  | 5, 0, 1 => 0x4b20cfa58240a0096419608232940106581dca63f280259065dac0885004b23ce92b8fca009e485ca531f94011e7494c7e1428025928722f4a65004b20cc65814ca009c419a2b03194010658270a63f280280a13614c7e5004da10b039994a0096485cc531f94012c833917c53280281215821c7e5
  | 5, 0, 2 => 0x4b23cef748fca0096419bcb03b14012c893918853280259212c94c7e5004b20cb748110a00a043560901f9400b04e14c7e2f2802590658240c25004b1c8531f868a009c4196073321401408f3a4a63f2802590d5ba407e5004b1606b298fca00832c120440a14012c832510656280259215821cfa5
  | 5, 0, 3 => 0x4b1d8b0398fca00581cca63f1914012c581cca64728028d287214c7e5004b14e7d3994ca00a0c1960733294013c90ac10e3f28020cfb581cca650053a28cb398fca00964adc8531f94012c832c8ec6528029d14582347e5004b1aeb0298fca0096391607d29940106581ccca5d2802810658240885
  | 5, 0, 4 => 0x4b1ca531f88ca00832c144531f94012c8337d607328028106582307e5004b20cc95f1ccb2c94390ca531f98014e832c11a5e280258a1461cc7e500419607331978b2c94290e6531f980106581cca03928025906582408850053a0ce0581ccb36832c0e6650a1801067e2c1385328028d285e9cca65
  | 5, 0, 5 => 0x419607331834a00832c1065f29940143832c0e66528026d06581ccca5a741960732f050c00a5ca1c8531f9401287214c7e1428025908591ccca5004e60cb048110a00832c0e6532094010658270bc5328025928642f4e65004195873298fca0096384e6531f94012c832c1143f280265065aa0ca65
  | 5, 0, 6 => 0x4da0cb03b194a009641960733114012c72384a63f28020cb04e194085005020cb03b194a009b419a2b0329659287214c7e1a300258993994c7e5004d96073328bca00832c0ec650a14014f832c0e6612cb20cb03b1942869b419607332838c00a04a1c8531f94012c89321887328020cb04698c7e5
  | 5, 0, 7 => 0x25906682c0ca50041960732f810a009641960763294012c521cca63f28020ccf5814c7e5004da0cde581cca008d36ce6531f94014e832c0e65e280259287214c7e5004b2505b298fca0096395c8531f940106581ccca0e28028706581d8ca5
  | 6, 0, 0 => 0x4b20cef541cc7e6004fa0cb03994c7e69641960733314c7e7004b20ce9298fc4c6005020cb04794c7e6004b20cb83994c7e6004b20cc7581cc7e60050216b03994c7e60045e0cd15814c7e6004b242b0439cc7e6004b20ccc398fc446004b21e943994c7e6a74196073268fc287005020cef5820c7e6004b1608d298fc5e6004b244ea581cc7e6
  | 6, 0, 1 => 0x4b1ecb03994c7e6004b20cb04820cca60052e0cb03994c7e6004196073298fc28600419a2b0298fc186004b20cd15821c7e6004196081298fc286004b21a943994c7e6003bd60731f8bc286004b20cb0480fc326004b20cbc5814c7e6004b20cf8581cca66005020cb03e9cca66004e20c943994c706004b250fc509cca66005020cb03994c786
  | 6, 0, 2 => 0x419607332970086004196070298fc186005020cb0399907e6004b20cb03994c866004b21c913994c7e6004b20cb03995c7e60051a24b03994c7e6004b20cae3994c7e6004e21eb03994c706004256073298fc2460051a0cbd581cca66004b20ce73994c7e6004b16073328bc086004b142733614c7e6004da0cef581cc7e6004b20cc43994c546
  | 6, 0, 3 => 0x50242b03394c7e6004b20cba3994c7e6004b216ef581cc7e600419deb03c1cc7e6005020cfc581bca66004b20cd1581940860051e0cfc551cca66004b20cb54194c2a6004b190b0398fc5e6004b20cb03a14c7e6004b20c943994c886004b23ca73994c7e60000259217294c7e500419ded1580fc286004b20cd16594c7e6004b250e45094c7e6
  | 6, 0, 4 => 0x4b20cb03a94c7e6005160cb03994c7e6004b1ba943994c7e6004b20cb73994c7e6005020cd65814c7e6004b20cb0399447e6004b1eeb03994c7e6004ce0cb03994c7e6004496073298d0286004196073298fc266004b20cef581f4e66004b20c9439978a660054602943994c7e6004b20cb04e14c7e6005020cb03614c7e6004b216b0399587e6
  | 6, 0, 5 => 0x5020cb04094c7e60051e0cc13994c7e6004196073319707e600501deb0398fc5e6004b20cfc5a9cca66004b20ccc529cc7e6004b16073298fc606004b242e55814c7e6004b20ccc398fc406a04b22d06582407e7004b20cb0431cc7e6005020cb03894c7e6004b250bd509cca66004b20cd1642c07e6000020cb04e14c7e50054606b03994c7e6
  | 6, 0, 6 => 0x4b1d2531f8bc4c6004b20cb03c94c7e6005020cb04194c7e600529bab03994c7e6004b210b23994c7e6004b20cc33994c7e6004b20cb13994c7e6005020caf3994c7e6004b242ef5819c7e6004b20cd15818c7e60051a0c943994c7e6004b22cb0399287e6004b237067494c7e6005020cb03994c7e6005022d06582407e6004b24b06621cca66
  | 6, 0, 7 => 0x41960732f14c706002c0e6531f8bc286004b60ce9298fc4c6004b20cbe539cca66004b20cb03b194086004b210943994c7e6004b23c943994c7e6004b20c923994c7e6004b20cfc58234a66004b160901f8bc326004b242b03494c7e6004b16073298fc5c600419f8b03994c186004b16073298fc5a6005020cef68ac07e6004b23ce93994c7e6
  | 6, 0, 8 => 0x4b228cb3994c7e6004b20ce95394c7e6004b20cef581cc7e600419f8ef581cc286004b20cfc659cca66004b208b03994c7e60050224b03994c686004b160732b8fc5e6004b21ab0481cc7e60050e0cb03994c7e6004da0cb03994c7e6004b242b03e99ca66005020cb04813c7e6005020cef581c07e6004b228b04694c7e6832c0e65c298fc287
  | 6, 0, 9 => 0x4b14273298fc346004ca0cef581cc7e6004b20cb0419587e6004b20cb0481cc8860041960783994c7e6004660cb03994c7e6004196073298fc2e6005022ab03994c7e600419dece581cc7e600419a2b0298fc286004b60cb03995c7e6004056073298fc026004196073268fc046004196081299347e6004b20cb0399587e6004d60cb03994c7e6
  | 6, 0, 10 => 0x5020cb03c14c7e6004f20cef581cc7e6004b20cb04194c4e6004b224c4509cca66004ca16b03994c7e6004b224ef581cc686004e60cb0480fc326004b20ced581cc7e600419609c2e14c7e6004b250dd3994c7e696419c8b03294c7e7004b20cd95314c7e6004b16073298fc626004b20cfc642c0e66004b20cb03994c786004ca0cb0399587e6
  | 6, 0, 11 => 0x4b20cc23998c7e6964196076298fc287004b20cdb3994c7e6004b255065820ca669b4196073298fc1c7005020cfc77ac0e66004196083298542860053a0cb0399787e60051e0cad3994c7e6004b16073299207e6964194e733294c7e7005016073298fc5e6004b20cd15b94c7e6004b20cfc581ccc66004b20cb0399907e6004b20ce4642c07e6
  | 6, 0, 12 => 0x4b243067294c7e6004b224c8581cc7e6004b20cb33994c7e6004b20ce0581cca66004b20cc85eac0e66004b22cd1581287e60041960733414c7e6004b20cde581cc086004196076298fc286004b2509e3994c7e6005020cd15814c7e6004b160a13e9cca66004196073298fc226004a60cb03994c7e6004b20cb0399507e6005016083298fc5e6
  | 6, 0, 13 => 0x51a50a13994c7e600419b0b03994c7e60034560531f8bc286004516073298fc286004b20cb03994c7e6004192873298fc186004e20cb03994c726004b20cb04094c7e600419f8b03994c2860053a0cb0399347e6004b1deb0398fc5e6004b20cfc58240326004b256a13994c7e6005020cb03814c7e6004d96073298fc5e6004b222b03994c7e6
  | 6, 0, 14 => 0x4b1607d3994c5e6004b20cd1581587e60052e0ce45814c7e600419c8b0298fc286004ca0cb03994c7e6005020cb03f94c7e6004b20cef68ac07e600419c4b03994c7e6004b23ab03994c7e6002c0f073298fc5e6004b20cb239994086004199cb03994c7e6004da0cd15814c7e6004b20cd45814c6c6004b20cf2581cc7e600419deb0399707e6
  | 6, 0, 15 => 0x4194e73298fc286005020cb03b14c7e6005020cce5814c7e60054e06b03994c7e6004b20ce46214c7e600419a2b03c14c7e6004b20cf4581b47e6004b218b03994c7e6004b20cb0441cc7e6004b20cb03b1947e6004b20cb04813c7e6004ca0cb04194c7e600419b4b03994c7e6004b20cd55814c7e600419ded1672c07e6005020cb04194c2a6
  | 6, 1, 0 => 0x419b6732e14c7e600501a2b0298fc5e6005020cb04f94c7e6004e20cb039970a66004b20cb046978a660050228b03994c7e6005020cfc581cca66004b20ab03994c7e6004b20cb039968a66004b214943994c7e6004b20cb63994c7e6004197ab03994c286004e60cef581cc7e6004b20c973994c7e6004d20cee581cc7e6004f20cb03994c7e6
  | 6, 1, 1 => 0x4b20cb03994c806004b20cbf3994c7e6004b224b03994c7c6005020ce45814c7e6004b20cef581d87e6004b20ca93994c7e6005020cbb5814c7e6004b20ce5439cc7e6004196073298fc1c60050e0cb03b14c7e6004b20ceb581cca66004da0cb03b14c7e6004e20cb03998c7e6005020cfc5820ca66004b20cb0419582a6004b242b03614c7e6
  | 6, 1, 2 => 0x5020ca73994c7e6004b20cfc581ccac6004b1607c298fc526003396073298fc5e60041960732e14c7e6004b20cfc77ac0e66005020cb041994a66004196473298fc2860053a0cb0399387e600002590658240885005020cb03d14c7e60050a0c933994c7e6004c60cb03994c7e6004b16073298fc5e6004e20cb03998c706005016070298fc5e6
  | 6, 1, 3 => 0x4f16073298fc5e6004196090298fc186004ca0cd15814c7e6004b20cb0459cca6600419a2ce5814c7e6004b20cef722c07e6004da0cb039994a66004de0cb03994c7e6004b20cd15814c7e6005020cbd581cca66004b20cf0581cc7e6004c96073298fc5e60053a0cd1581347e6004b1ded1580fc5e6004b228ef581cc7e6004ee0cb03994c7e6
  | 6, 1, 4 => 0x4196073298fc206004b16073298fc586004b20cb03b14c7e6004b21ab73994c7e60041960732f14c286004b1d2dd298fc4c6004b251217494c7e6005020cb23994c7e69641960732f14c287964a142733294c7e7004ea0cfc581cca6600419607329910286004f20cd15814c7e6004b20cef539cc7e6004b20cb0461cc7e6004356073298fc286
  | 6, 1, 5 => 0x4b20cef591cc7e600250e6531f8bc286004b1a2b0298fc5e6004b228b03994c7e6004b1bac43994c7e6004da0cb23994c7e6004b20cfc58204a6600419ca73298fc28600419a6b03994c7e6002c0e65c298fc5e60053a0cfc581cc9a6004b56073298fc5e6004b1f8ef581cc5e6004b20cb03714c7e6004b22c94399287e6004196073298fc126
  | 6, 1, 6 => 0x4b20eb03994c7e6004b20ca73994c7e6005020cb039978a66004b20ccc3d9cc7e6004b20cb03994c7a6005456073298fc666005020cb03994c886004b20ce45814c7e6004b20cb02d94c7e6005020cb03914c7e6004b23ce9298fc4c6003459cb0298fc5e6004c20cb03994c7e600419a2b02e14c7e6004b20cfc77b45606004b20cb04714c7e6
  | 6, 1, 7 => 0x4f60cb03994c7e6004b20cb23994c7e6004b20cef729cc7e69c4b20cb03994c847004b20cb041958a66004b250e43994c7e6004b16076298fc5e6005012873298fc5e6004b20c963994c6a6000026d06581ccca5005020ce53994c7e6004b20cb0399942c6004b20cd05814c7e6004da5906581ccca6004a14273298fc286004b20cbd581cca66
  | 6, 1, 8 => 0x53a0cf3581cc7e6964a14273298fc34700419607332850086004b20cd15394c7e6964196073328500870052a0cb03994c7e6004b20ce4298fc4c6004196087398fc286004b20c58298fc4c6004e20cb04094c706004e20cb04094c7e60051a0cef581cc7e60050250a13994c7e6004b1c8b0298fc5e6004b1de94398fc5e600419a6d15814c7e6
  | 6, 1, 9 => 0x5020cb03999408600419609a3994c7e6004b20cbb580fc326004b20cd15914c7e6004b20cb04194c2c600419609c3294c7e6004b20cf1581cc7660051a0cb03994c7e6004b12873298fc5e6004b20ce53994c7e6004b20c853994c3a60041960732a8fc1e6004b20cb039978a660054602b03994c7e6004b20cb03b1ccca6004b20cb0399949c6
  | 6, 1, 10 => 0x4b20cb23b14c7e600419609b3994c7e6004b20cb04194c366000029d06581ccbc5004b20cb0439f4e66005220cce5814c7e6004da0cb039994086004b20ce45394c7e60053a5906581ccbc60000259287214c7e5004b250a13994c7e600419d2531f898286004b1caa13994c7e60053e0cb03993c7e6004f20ce53994c7e60041960a33994c7e6
  | 6, 1, 11 => 0x25906581d8ca5005325906581ccca69b4196073298fc287004196073298fc18600419609c3994c7e60051a0cd15814c7e6004b20c732c94c7e6005020cd25814c7e6004b1a294298fc5e6004b20ce56894c7e6004b1ba73298fc4c6004b96073298fc5e6004b250e45814c7e60054602d15814c7e6004196078298fc0e6005020cb03794c7e6
  | 6, 1, 12 => 0x51a0ce45814c7e60053a7106581ccca6004196078298fc1860041960732f94c7e6004fe0cb03994c7e6004b20ce35814c7e6004b20cb039994086004b250d15094c7e6
  | 7, 0, 0 => 0x4b20cfc68ac0a63f38000106581cca63f0a180152964196073298fce00a74b20cb0399947e7a74b20cb03994c7e024002590668ac154531f9c00009641960901f864c009641960733614c7e7004b20cef581cc7e1d3802810680ac0e6531f9c012c90ac0e667298fce00964196073298fc2870051e5906621cca63f3800012c833a4a63f1318012c833f160733794ce00964a20cfc581cca67
  | 7, 0, 1 => 0x4b20cb0399c4a63f380258b03994c923f179c012c832512873298fce00004b20cb03995c7e60054e8106581cca63f38025906581cca63f041c012c833bd6073268fce00a75020cb03994c7e7004b160733294c7e2f3802590668ac0ce531f9c0144a04196073298fce00a0419a2b03994c7e7004b20cd6581cca63f38025906581cca63f119c012c832c0e653260fce0096419d2943994c7e7
  | 7, 0, 2 => 0x4b20cb03994c7e363802590668ac0ca531f9c012c833296073298fce009641960933994c7e7004b20cb0399cca63f3802590674ac0a63f131c012c8b4196090398fce009c4196073298fc707004b20cb0409cca63f380259067fac0e6531f9c012c83250e6531f8e0e00a041960733814c7e7004b16073298fc5e2938025906581cca6521f9c0106581ccca5c298fce009641a00b03994c7e7
  | 7, 0, 3 => 0x4b20cb03994c883f38029d2c833bd60731f9c012c833bda2b0398fce009641960733514c7e70000259065b9cca63f3002a32c581cca63f179c012c832c10673298fce00964620cd15814c7e7004b20cfc581cca6153802590680bbd60731f9c0106662c0e6531f850e00a3d020cb03994c7e7004b20cb0401cca63f3802590f581cca63f1c1c012c581cca63f17884e00964196073298fc507
  | 7, 0, 4 => 0x4b1d2dd581cca63f3800012c8b2c0e64a1f980140964196083298fce009641960732f14c7e7000028106581cca63f3002a32c8334560531f9c012c833bd6073380fce00832c0e6531f864287004b20cb03994ca63f38025906622c0e6531f9c012c833356073298fce00964196073298fc047004b20ccc621cca63f380258ef581cca63f179c0140964196073298fce009641960963994c7e7
  | 7, 0, 5 => 0x4b20cfc581ccce5338026d2c832c0e6531f9c0140832c0e6531f8e4f409641998b03994c7e8004b20cb03994c7e373802590662ac0e6531f9c012c833f1f8b03994ce0096419f8f5581cca67004b225064a1cca63f3802932c832c0e6531f9c012c581cca63f17850e00005020cb04194c7e6004b20cb7581cca63f38025913832c0e6531f9c0106581cca63f0a048e00a3cb20cef581cc7e7
  | 7, 0, 6 => 0x2590677ac0e63f3002590668ac0a63f0a1c012c832c0e6531f8e8e00964a20c943994c7e7004b20cb03994c9a3f380259065b9cca63f0c9c012c834096073298fce00004da0cb03994c7e6004b20cb9581cca63f38028106662c0e6531f9c012c94419d273298fce00002c0e6531f8bc286004b20cd158298a63f38025906581cca63f0e9c012c832c0e6531f858e00964260cb03994c7e7
  | 7, 0, 7 => 0x4b20d01581cca63f38020cb03994c7e340a1e590658284e665298fd0000041960783994c7e6004b20cb03994c7e0b38028106581cca63f0c9c0156832c0e6531f850e00964196073298fc347004b20cd668ac0a63f3800010668ac0a63f0a18012c832c0e6531f890e009641960783994c7e7004b20cfc581ccca5338025906581cca64b1f9c00009641960732b0fcc009641960ab3994c7e7
  | 7, 0, 8 => 0x419a2ce581cca63f38025906581cca63f129c012c8332160a1398fce00a9cb20cb03994c7e7004b20c943994c943f3802812c581cca63f179c014e964196073298fce0096419a2b0298fc6c7004b24706581cca63f3802892c832c0e6531f9c012c833bd98b0398fce0096419a2b03994c7e7004b22506622c0e65338025921833a560531f9c012c833c5deb0398fce00962c10673298fc5e7
  | 7, 0, 9 => 0x4b20cb03994c7e1c38025906581ccae3f131c012c8334588b0298fce00a3cb20cb03994c7e7004b20cfd581cca63f3802812c8334560531f9c0106581cca63f0a000e00832c0e6531f898287004b20cfc77ac0e65338000140581cca63f1798012c833716073298fce0096419e8ef581cc7e7004b20cb0399c0a63f3802590668ac106531f9c012c832c0e6531f86ce00964192873298fc2a7
  | 7, 0, 10 => 0x4b172b03994c7e2f3802592c832c0e6531f9e5906581cca63f0a0110009641960833994c2a7004b20cfc581cca61438029d2c832c0e64d1f9c012c95c196073298fcf2c90c1960733294c7e8005025906581c0a63f38025920832c0e6531f9c012c832c0fe73298fce00964196073298fc567004b20cde581cca63f380001408334560531f98012c924196073298fce00a6cb20cb03994c7e7
  | 7, 0, 11 => 0x20cce581cca63f3002652c832c0e6531f9c012c83250e667298fce009641960763994c7e7004b20cb03994c9c3f3802590668ac0a63f0e9c012c833396073298fce00004b20cb03994c7e6004196073298fc28043800012c832c102531f980000833f1607329850c000053a0cb0399347e6004b20caa4a1cca63f3800012c77ac0e63f17980000a04196070298fcc00a04196073298fc687
  | 7, 0, 12 => 0x4b20cc4509cca63f3802792c832c0e6531f9c012c68ac0e6531f8bce0096419609f3994c7e7004b20cc0581cca63f38028106581cca63f131c015696419deb0398fce00964196073298fc727000026506581cca63f3000012c833bda2b01f98012c832c12273298fce0096419a2b0299347e7004b20cd9581cca63f380259067e2c0e653291c012c832c15a73298fce00832c14273298fc287
  | 7, 0, 13 => 0x4b20cef581cc7e1f38025906581ccca3f021c014e96419a2b0298fce0096419a2d15814c7e70050259067e2c0e6533802591f832c0e6531f9c012c833bddcb0398fce00962c0e670298fc5e7004b20ce4581cca63f3800013c832c0e6531f98012c832c14073298fce009641976b03994c7e7004b20cfc5820ce65338025906582c0e6531f9c012c8b4196073250fce00a74b16073298fc5e7
  | 7, 0, 14 => 0x4b23906581cca63f38025906729ccce531f9c012c832c10873298fce00a4cb20cfc581cca67005020cb0509cca63f38020cb0481cca63f0a1c0121832c0e6531f850e0096419a2b03814c7e7004b20cef581cc7e00380259065820ce665299c0140832c0e6531f810e00005020cfc581cca660051e58b03994c7e2f38020cb03994c7e2f0a1c012c832c0f473298fce00964196073298fc327
  | 7, 0, 15 => 0x4b20cd1672c0a63f38025906752c0e6531f9c000096419a2b0298fcc0097cb20cb03994c7e7004e20cb03994c7e143802590677ac0e63f021c0000832c0e65c298fcc00004b20cfc77ac0e66004b20cfc581cca64d38026d06581cca63f021e712c832c0e6531f851000964196073299147e7004b20cb039970a63f3800012c581cca63f1798012c832c0e6531f818e00a84b20cb03994c7e7
  | 7, 1, 0 => 0x4b24d06581cca63f38025906661cca63f0f9e5906581cca63f1c05100096419dcb03994c7e7004b20c94499cca63f38029d2c833f16073299c0140832c12073298fce00a04860cb03994c7e7004b20cb03994c7e1838020cb03994c843f0a1c0000833459cb0298fcc00a04196073298fc5e70055a5906581cca63f3802590677ac142731f9c012c832c0e6631f8e0e00a041a06b03994c7e7
  | 7, 1, 1 => 0x4b20cb0399c8a63f3800012c832c0ec531f98014c964196073298fce00964860cef581cc7e7005565906581cca63f38025924833f16073299c012c8334560531f864e00964196073298fc147004b20cc44a1cca63f3802590677ac0e63f179c012c832c0e6531f800e00964196073298fc4c7004b20ce9621cca63f38020cb03994c7e380a1e5928832c0e665298fd00096419d0b03994c7e7
  | 7, 1, 2 => 0x4a20cb03994c7e143802ad2c8334560531f9c012c833f198b03994ce009649e0cb03994c7e7005020cb03994c7e383800012c8339160531f98012c832c14273298fce00ab4b16073298fc5e70000258d15814c7e2f3000012c8a2c0e6531f98012c83250e6531f874e0097cb16073298fc5e7004e60cb03994c7e1938025906581cca63f021c0106581cca63f0a01ce00964196073299187e7
  | 7, 1, 3 => 0x4196073298fc28053802590679ac0e6531f9c0106581cca64d1f8e0e00964860cb03994c7e7004b20cb03994c7e033802590658260e6531f9c012d832c0e6531f898e00a74e20cb03994c7e7004b20cb03994c7e2f38025906581cca63f0f1c012c833f1607329864e00962c0e6531f8bc0070000259065eac0e65330025906612c0e6531f9c0000964194e73298fcc009641a02943994c7e7
  | 7, 1, 4 => 0x4b20ca13994c7e2638025906592c0e6531f9c0106582a8e6531f850e009641928913994c7e7004b20cb03994c843f3802590668ac142531f9c012c8334560531f810e00962c14273298fc5e7005025106581cca63f3800012c832c8e6531f98012c954196073298fce00962c0e6531f8bc087004b20cb04820ca63f3802912c832c0e6531f9c012c832c14e73298fce0096419a2b0298fc007
  | 7, 1, 5 => 0x25906729cca63f3002912c8334560531f9c0140832c0e6531f830e00964196073298fc0e7004b2430668ac0a63f38025906581d8a63f021c00009641960732f14cc000054602b03994c7e6004b20cd15814c7e2f38020cb039994a63f0a1c0151964056073298fce009641960953994c7e7964a20cb03994c7e1a4002590658204a63f1c1e5906581ccca531f851000833f16073298fc287
  | 7, 1, 6 => 0x4b20cb0399bca63f38025906642c0e6531f9c0106581cca63f0a050e00962c12873298fc5e7004b25106581cca63f38025906722c142531f9c012c74ac0e6531f8bce0096419cab03994c7e7005020cb039994a63f38000146832c0e6531f98000096250e6531f8bcc00a0419f8b03994c7e7005460cb03994c7e1438025906581ccac3f0a9c01065a2c0e6531f850e00a34b20cb03994c7e7
  | 7, 1, 7 => 0x5020cb0399cca63f380259067e2c0e6531f9c0000832c0e6531f830c00964196073298fc1870051e0cb0551cca63f380259065820ca63f0a9c0140832c0e6531f850e00964196473298fc087004b250b0509cca63f38025906692c0e6531f9c012c83250e6531f898e00964196073298fc0a7004b20cfc58240e653380258b03e1cca63f179c0154964196073298fce00004b250a13994c7e6
  | 7, 1, 8 => 0x146832c14273298fce00832c0e670298fc287004b20cb04f1cca63f38020cd1581cca63f0a1c0151a3c196073298fce00a05020cb03994c7e7004b20cb039994a63f3800012c832c0e66502180106581e0e6531f850e00964a20cd15814c7e7
  | 8, 0, 0 => 0x964196073298fc327004b20cb03994c7e6a3cb20cb03994c7e79641960733814c7e7a74b20cb03994c7e796419a2b03994c7e79641a02b03994c7e7004b20cef581cc7e6964196073299347e7964196073298fc3a7005020cb03994c7e69641988b03994c7e7a04b20cb03994c7e79641960833994c7e7004196073298fc286964196073298fc287
  | 8, 0, 1 => 0x9641960733294c7e796419f8b03994c7e7964a20cb03994c7e7964860cb03994c7e7964196073298fc5e79641960a13994c7e7964196073298fc087964196073298fc4c7004b20cd15814c7e6004b16073298fc5e6
  | 9, 0, 0 => 0x4b20cb03994c7e6
  | _, _, _ => 0

def stateWidth : Nat → Nat
  | 3 => 32
  | 4 => 41
  | 5 => 59
  | 6 => 68
  | 7 => 77
  | 8 => 68
  | 9 => 59
  | _ => 0

def idWidth : Nat := 9

def wireAt (i : Nat) : Nat :=
  fld (dictionaryBlocks (i / 128) (i / 8 % 16)) 84 (i % 8)

def stateWires : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, ids => wireAt (fld ids idWidth 0) :: stateWires n (ids >>> idWidth)

def S (s j : Nat) : List Nat :=
  let packed := fld (stateBlocks s (j / 256) (j / 16 % 16)) (stateWidth s) (j % 16)
  stateWires (packed &&& 31) (packed >>> 5)

def symsG : List (List (Nat × Nat)) := [[(0x4000004000100000100, 1), (0xf0000000003c00000000, 4), (0x3ff00000000ffc00, 10)], [(0x111000001004440000040, 1), (0x1c0000000007, 3), (0xf03c0000003c0f000, 4)], [(0x5000005000140000140, 1), (0x200000001c0800000007, 3), (0xc0000000003000000000, 4), (0x10000000000400000000, 5), (0x3c000000000f0000, 6), (0x30000000000c00, 10), (0x3c000000000f000, 14)]]

theorem symsG_ok : symsG.all (fun ms => ms.all (moveOK 42)) = true := by decide +kernel

def ori (zs : List Nat) : List Nat :=
  pickMin 1000003 zs symsG zs (hk 1000003 zs)

theorem ori_ok {u ys} (h : NatRunT 42 false (goal 42) u ys) :
    NatRunT 42 false (goal 42) u (ori ys) :=
  pickMin_runT 1000003 ys h symsG ys (hk 1000003 ys) symsG_ok h

def idx (s : Nat) (zs : List Nat) : Nat :=
  bsr (fun i => fld (HT s (i / 64)) 32 (i % 64)) (hk 1000003 zs) 10 0 (NN s)

def poolG : List Nat := [42821612120099893, 29315202688264239, 13548199506651180, 29286623974832170, 33801227309468715, 33794625947879470, 18047396788348974, 33801199401610291, 33794617364232242, 29297619092159530, 29297623387126826, 18027633497389098]

def Z (s : Nat) := bar 42 false S NN idx ori poolG s

private theorem z0 : ∀ i, 0 ≤ i → i < 0 → Z 0 i = true := by omega

private theorem z1 : ∀ i, 0 ≤ i → i < 0 → Z 1 i = true := by omega

private theorem z2 : ∀ i, 0 ≤ i → i < 0 → Z 2 i = true := by omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i, 0 ≤ i → i < 1 → Z 3 i = true := span_ok (by decide +kernel : span (Z 3) 1 0 = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i, 0 ≤ i → i < 10 → Z 4 i = true := span_ok (by decide +kernel : span (Z 4) 10 0 = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_0 : ∀ i, 0 ≤ i → i < 12 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 0 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_12 : ∀ i, 12 ≤ i → i < 24 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 12 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_24 : ∀ i, 24 ≤ i → i < 36 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 24 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_36 : ∀ i, 36 ≤ i → i < 48 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 36 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_48 : ∀ i, 48 ≤ i → i < 60 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 48 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_60 : ∀ i, 60 ≤ i → i < 72 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 60 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_72 : ∀ i, 72 ≤ i → i < 84 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 72 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_84 : ∀ i, 84 ≤ i → i < 96 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 84 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_96 : ∀ i, 96 ≤ i → i < 108 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 96 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_108 : ∀ i, 108 ≤ i → i < 120 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 12 108 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z5_120 : ∀ i, 120 ≤ i → i < 125 → Z 5 i = true := span_ok (by decide +kernel : span (Z 5) 5 120 = true)
private theorem z5 : ∀ i, 0 ≤ i → i < 125 → Z 5 i = true := (range_split (range_split (range_split z5_0 z5_12) (range_split z5_24 (range_split z5_36 z5_48))) (range_split (range_split z5_60 (range_split z5_72 z5_84)) (range_split z5_96 (range_split z5_108 z5_120))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_0 : ∀ i, 0 ≤ i → i < 12 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 0 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_12 : ∀ i, 12 ≤ i → i < 24 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 12 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_24 : ∀ i, 24 ≤ i → i < 36 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 24 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_36 : ∀ i, 36 ≤ i → i < 48 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 36 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_48 : ∀ i, 48 ≤ i → i < 60 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 48 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_60 : ∀ i, 60 ≤ i → i < 72 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 60 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_72 : ∀ i, 72 ≤ i → i < 84 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 72 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_84 : ∀ i, 84 ≤ i → i < 96 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 84 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_96 : ∀ i, 96 ≤ i → i < 108 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 96 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_108 : ∀ i, 108 ≤ i → i < 120 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 108 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_120 : ∀ i, 120 ≤ i → i < 132 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 120 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_132 : ∀ i, 132 ≤ i → i < 144 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 132 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_144 : ∀ i, 144 ≤ i → i < 156 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 144 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_156 : ∀ i, 156 ≤ i → i < 168 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 156 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_168 : ∀ i, 168 ≤ i → i < 180 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 168 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_180 : ∀ i, 180 ≤ i → i < 192 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 180 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_192 : ∀ i, 192 ≤ i → i < 204 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 192 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_204 : ∀ i, 204 ≤ i → i < 216 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 204 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_216 : ∀ i, 216 ≤ i → i < 228 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 216 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_228 : ∀ i, 228 ≤ i → i < 240 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 228 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_240 : ∀ i, 240 ≤ i → i < 252 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 240 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_252 : ∀ i, 252 ≤ i → i < 264 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 252 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_264 : ∀ i, 264 ≤ i → i < 276 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 264 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_276 : ∀ i, 276 ≤ i → i < 288 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 276 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_288 : ∀ i, 288 ≤ i → i < 300 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 288 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_300 : ∀ i, 300 ≤ i → i < 312 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 300 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_312 : ∀ i, 312 ≤ i → i < 324 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 312 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_324 : ∀ i, 324 ≤ i → i < 336 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 324 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_336 : ∀ i, 336 ≤ i → i < 348 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 336 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_348 : ∀ i, 348 ≤ i → i < 360 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 348 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_360 : ∀ i, 360 ≤ i → i < 372 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 360 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_372 : ∀ i, 372 ≤ i → i < 384 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 372 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_384 : ∀ i, 384 ≤ i → i < 396 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 384 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_396 : ∀ i, 396 ≤ i → i < 408 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 396 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_408 : ∀ i, 408 ≤ i → i < 420 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 408 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_420 : ∀ i, 420 ≤ i → i < 432 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 420 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_432 : ∀ i, 432 ≤ i → i < 444 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 432 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z6_444 : ∀ i, 444 ≤ i → i < 456 → Z 6 i = true := span_ok (by decide +kernel : span (Z 6) 12 444 = true)
private theorem z6 : ∀ i, 0 ≤ i → i < 456 → Z 6 i = true := (range_split (range_split (range_split (range_split (range_split z6_0 z6_12) (range_split z6_24 z6_36)) (range_split (range_split z6_48 z6_60) (range_split z6_72 (range_split z6_84 z6_96)))) (range_split (range_split (range_split z6_108 z6_120) (range_split z6_132 (range_split z6_144 z6_156))) (range_split (range_split z6_168 z6_180) (range_split z6_192 (range_split z6_204 z6_216))))) (range_split (range_split (range_split (range_split z6_228 z6_240) (range_split z6_252 z6_264)) (range_split (range_split z6_276 z6_288) (range_split z6_300 (range_split z6_312 z6_324)))) (range_split (range_split (range_split z6_336 z6_348) (range_split z6_360 (range_split z6_372 z6_384))) (range_split (range_split z6_396 z6_408) (range_split z6_420 (range_split z6_432 z6_444))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_0 : ∀ i, 0 ≤ i → i < 12 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 0 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_12 : ∀ i, 12 ≤ i → i < 24 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 12 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_24 : ∀ i, 24 ≤ i → i < 36 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 24 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_36 : ∀ i, 36 ≤ i → i < 48 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 36 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_48 : ∀ i, 48 ≤ i → i < 60 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 48 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_60 : ∀ i, 60 ≤ i → i < 72 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 60 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_72 : ∀ i, 72 ≤ i → i < 84 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 72 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_84 : ∀ i, 84 ≤ i → i < 96 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 84 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_96 : ∀ i, 96 ≤ i → i < 108 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 96 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_108 : ∀ i, 108 ≤ i → i < 120 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 108 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_120 : ∀ i, 120 ≤ i → i < 132 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 120 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_132 : ∀ i, 132 ≤ i → i < 144 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 132 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_144 : ∀ i, 144 ≤ i → i < 156 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 144 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_156 : ∀ i, 156 ≤ i → i < 168 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 156 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_168 : ∀ i, 168 ≤ i → i < 180 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 168 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_180 : ∀ i, 180 ≤ i → i < 192 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 180 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_192 : ∀ i, 192 ≤ i → i < 204 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 192 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_204 : ∀ i, 204 ≤ i → i < 216 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 204 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_216 : ∀ i, 216 ≤ i → i < 228 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 216 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_228 : ∀ i, 228 ≤ i → i < 240 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 228 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_240 : ∀ i, 240 ≤ i → i < 252 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 240 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_252 : ∀ i, 252 ≤ i → i < 264 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 252 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_264 : ∀ i, 264 ≤ i → i < 276 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 264 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_276 : ∀ i, 276 ≤ i → i < 288 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 276 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_288 : ∀ i, 288 ≤ i → i < 300 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 288 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_300 : ∀ i, 300 ≤ i → i < 312 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 300 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_312 : ∀ i, 312 ≤ i → i < 324 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 312 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_324 : ∀ i, 324 ≤ i → i < 336 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 324 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_336 : ∀ i, 336 ≤ i → i < 348 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 336 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_348 : ∀ i, 348 ≤ i → i < 360 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 348 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_360 : ∀ i, 360 ≤ i → i < 372 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 360 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_372 : ∀ i, 372 ≤ i → i < 384 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 12 372 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z7_384 : ∀ i, 384 ≤ i → i < 394 → Z 7 i = true := span_ok (by decide +kernel : span (Z 7) 10 384 = true)
private theorem z7 : ∀ i, 0 ≤ i → i < 394 → Z 7 i = true := (range_split (range_split (range_split (range_split (range_split z7_0 z7_12) (range_split z7_24 z7_36)) (range_split (range_split z7_48 z7_60) (range_split z7_72 z7_84))) (range_split (range_split (range_split z7_96 z7_108) (range_split z7_120 z7_132)) (range_split (range_split z7_144 z7_156) (range_split z7_168 z7_180)))) (range_split (range_split (range_split (range_split z7_192 z7_204) (range_split z7_216 z7_228)) (range_split (range_split z7_240 z7_252) (range_split z7_264 z7_276))) (range_split (range_split (range_split z7_288 z7_300) (range_split z7_312 z7_324)) (range_split (range_split z7_336 z7_348) (range_split z7_360 (range_split z7_372 z7_384))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z8_0 : ∀ i, 0 ≤ i → i < 12 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 0 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z8_12 : ∀ i, 12 ≤ i → i < 24 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 12 12 = true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z8_24 : ∀ i, 24 ≤ i → i < 26 → Z 8 i = true := span_ok (by decide +kernel : span (Z 8) 2 24 = true)
private theorem z8 : ∀ i, 0 ≤ i → i < 26 → Z 8 i = true := (range_split z8_0 (range_split z8_12 z8_24))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i, 0 ≤ i → i < 1 → Z 9 i = true := span_ok (by decide +kernel : span (Z 9) 1 0 = true)

theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => z0 i (Nat.zero_le i) hi
  · exact fun i hi => z1 i (Nat.zero_le i) hi
  · exact fun i hi => z2 i (Nat.zero_le i) hi
  · exact fun i hi => z3 i (Nat.zero_le i) hi
  · exact fun i hi => z4 i (Nat.zero_le i) hi
  · exact fun i hi => z5 i (Nat.zero_le i) hi
  · exact fun i hi => z6 i (Nat.zero_le i) hi
  · exact fun i hi => z7 i (Nat.zero_le i) hi
  · exact fun i hi => z8 i (Nat.zero_le i) hi
  · exact fun i hi => z9 i (Nat.zero_le i) hi

def RootG (s : Nat) : Bool :=
  scr 42 s poolG xsG || found S NN idx s (ori xsG)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 5 5 = true := by decide +kernel

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : NatRunT 42 false (goal 42) s xsG) : False := by
  have hmin : 5 ≤ s := by
    have hl := runT_len h
    change 6 ≤ s + 1 at hl
    omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no poolG h, Bool.false_or] at hr
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hr
  exact bar_all ori_ok checked s hs _ hr.1 (RunT.perm hr.2 (ori_ok h))

theorem noCircuit : ¬ HasCircuitSize 6 fG 9 := mainG noRunFull

end Main

end PEqualNP.Outside.L_meta_38157_aux

namespace PEqualNP.Outside.L_meta_38157_aux

def monoC : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 14]⟩], 15⟩

theorem monoC_size : monoC.size = 10 := rfl

theorem monoC_mono : PEqualNP.MetaComplexity.Monotone2 monoC := by
  intro g hg
  simp only [monoC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem monoC_eval : ∀ x : Fin 6 → Bool, monoC.eval (List.ofFn x) = Nat.testBit (4294901486 * 2 ^ 32 + 4294506728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem hedge : ∀ x : Fin 6 → Bool, Nat.testBit (4294901486 * 2 ^ 32 + 4294506728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = Main.fG x := by decide +kernel

end PEqualNP.Outside.L_meta_38157_aux

theorem PEqualNP.Outside.L_meta_38157 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901486 * 2 ^ 32 + 4294506728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901486 * 2 ^ 32 + 4294506728) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  by_cases hL : 10 ≤ s
  · exact ⟨PEqualNP.Outside.L_meta_38157_aux.monoC, PEqualNP.Outside.L_meta_38157_aux.monoC_mono, by rw [PEqualNP.Outside.L_meta_38157_aux.monoC_size]; exact hL, PEqualNP.Outside.L_meta_38157_aux.monoC_eval⟩
  · exfalso
    apply PEqualNP.Outside.L_meta_38157_aux.Main.noCircuit
    obtain ⟨C, hfan, hsz, hev⟩ := hs
    exact ⟨C, hfan, by omega, fun x => (hev x).trans (PEqualNP.Outside.L_meta_38157_aux.hedge x)⟩
