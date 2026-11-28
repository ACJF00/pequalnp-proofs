import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1473_aux


namespace Build1470

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.NotBracket (notCount)

private abbrev Allowed (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .not

private def bitOrder (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false ≤ y.getD i false

private theorem bool_order (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

private theorem bool_digit (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

private theorem digit_order {a b : Bool} (ab : a ≤ b) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all [bool_order]

private theorem digit_inj {a b : Bool} (eq : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem order_append {x y : List Bool} (ordered : bitOrder x y) {a b : Bool} (ab : a ≤ b) :
    bitOrder (x ++ [a]) (y ++ [b]) := by
  refine ⟨by simp [ordered.1],?_⟩
  intro i
  rcases lt_trichotomy i x.length with lt | eq | gt
  · have ly : i < y.length := ordered.1 ▸ lt
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left ly] using ordered.2 i
  · subst i
    simpa [List.getD_eq_getElem?_getD,ordered.1] using ab
  · have noneX : (x ++ [a]).length ≤ i := by simp; omega
    have noneY : (y ++ [b]).length ≤ i := by simp [← ordered.1]; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none noneX,List.getElem?_eq_none noneY]

private def incoming (g : Gate) (w : List Bool) : List Bool :=
  g.inputs.map (fun i => w.getD i false)

private def outputBit (g : Gate) (w : List Bool) : Bool := g.op.eval (incoming g w)

private def firstBit (g : Gate) (w : List Bool) : Bool := (incoming g w).headD false

private theorem first_order (g : Gate) {x y : List Bool} (ordered : bitOrder x y) :
    firstBit g x ≤ firstBit g y := by
  unfold firstBit incoming
  cases h : g.inputs with
  | nil => simp
  | cons i rest => exact ordered.2 i

private theorem and_order {g : Gate} (op : g.op = .and) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.all_eq_true] at on ⊢
  intro v hm
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact (bool_order _ _).mp (ordered.2 i) (on _ (List.mem_map.mpr ⟨i,here,rfl⟩))

private theorem or_order {g : Gate} (op : g.op = .or) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.any_eq_true] at on ⊢
  obtain ⟨v,hm,active⟩ := on
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact ⟨_,List.mem_map.mpr ⟨i,here,rfl⟩,(bool_order _ _).mp (ordered.2 i) active⟩

private def inverting (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

private def advance (s : List Bool × ℕ) (g : Gate) : List Bool × ℕ :=
  (s.1 ++ [outputBit g s.1],if inverting g then 2*s.2+(firstBit g s.1).toNat else s.2)

private def consistent (s t : List Bool × ℕ) : Prop :=
  s.2 ≤ t.2 ∧ (s.2 = t.2 → bitOrder s.1 t.1)

private theorem advance_consistent {s t : List Bool × ℕ} {g : Gate} (allowed : Allowed g)
    (before : consistent s t) : consistent (advance s g) (advance t g) := by
  by_cases strict : s.2 < t.2
  · have increase : (advance s g).2 < (advance t g).2 := by
      by_cases neg : inverting g = true
      · simp only [advance,neg,ite_true]
        have bit := bool_digit (firstBit g s.1)
        omega
      · simpa [advance,neg] using strict
    exact ⟨increase.le,fun eq => (increase.ne eq).elim⟩
  have eq : s.2 = t.2 := Nat.le_antisymm before.1 (Nat.le_of_not_gt strict)
  have ordered := before.2 eq
  rcases allowed with op | op | op
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (and_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (or_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,ite_true]
    have order := digit_order (first_order g ordered)
    refine ⟨by omega,?_⟩
    intro next
    have sameDigit : (firstBit g s.1).toNat = (firstBit g t.1).toNat := by omega
    have sameBit := digit_inj sameDigit
    apply order_append ordered
    simp only [outputBit,op,GateOp.eval]
    change (!firstBit g s.1) ≤ (!firstBit g t.1)
    rw [sameBit]

private def negCount (gates : List Gate) : ℕ := (gates.filter inverting).length

private theorem negCount_spec (C : Circuit) : negCount C.gates = notCount C := by
  classical
  unfold negCount notCount
  congr 2
  funext g
  cases h : g.op <;> simp [inverting,h]

private theorem run_consistent (gates : List Gate) (allowed : ∀ g ∈ gates, Allowed g)
    {s t : List Bool × ℕ} (before : consistent s t) :
    consistent (gates.foldl advance s) (gates.foldl advance t) := by
  induction gates generalizing s t with
  | nil => exact before
  | cons g rest ih =>
    exact ih (fun k hm => allowed k (List.mem_cons_of_mem _ hm))
      (advance_consistent (allowed g (List.mem_cons_self ..)) before)

private theorem run_bounded (gates : List Gate) (s : List Bool × ℕ) (d : ℕ) (bound : s.2 < 2^d) :
    (gates.foldl advance s).2 < 2^(d+negCount gates) := by
  induction gates generalizing s d with
  | nil => simpa [negCount] using bound
  | cons g rest ih =>
    by_cases neg : inverting g = true
    · have raises : (advance s g).2 < 2^(d+1) := by
        simp only [advance,neg,ite_true,Nat.pow_succ]
        have digit := bool_digit (firstBit g s.1)
        omega
      have next := ih (advance s g) (d+1) raises
      simpa [negCount,neg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next
    · have same : (advance s g).2 < 2^d := by simpa [advance,neg] using bound
      simpa [negCount,neg] using ih (advance s g) d same

private theorem run_wires (gates : List Gate) (s : List Bool × ℕ) :
    (gates.foldl advance s).1 =
      gates.foldl (fun w g => w ++ [outputBit g w]) s.1 := by
  induction gates generalizing s with
  | nil => rfl
  | cons g rest ih => exact ih (advance s g)

private theorem inputs_order {n : ℕ} {x y : Fin n → Bool} (xy : x ≤ y) :
    bitOrder (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  have first : bitOrder (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,?_⟩
    intro i
    by_cases inside : i < n
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside] using xy ⟨i,inside⟩
    · simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside]
  simpa only [List.append_assoc,List.singleton_append] using
    order_append (order_append first (a := false) (b := false) le_rfl)
      (a := true) (b := true) le_rfl

def grade {n : ℕ} (C : Circuit) (x : Fin n → Bool) : ℕ :=
  (C.gates.foldl advance (List.ofFn x ++ [false,true],0)).2

theorem grade_bound {n : ℕ} (C : Circuit) (x : Fin n → Bool) : grade C x < 2^(notCount C) := by
  simpa [grade,negCount_spec] using
    run_bounded C.gates (List.ofFn x ++ [false,true],0) 0 (by change 0 < 1; decide)

theorem grade_order {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool} (xy : x ≤ y) :
    grade C x ≤ grade C y ∧ (grade C x = grade C y → ∀ i,
      (C.wires (List.ofFn x ++ [false,true])).getD i false ≤
        (C.wires (List.ofFn y ++ [false,true])).getD i false) := by
  have allowed (g) (mem : g ∈ C.gates) : Allowed g := by
    simpa [Allowed] using (basis g mem).1
  have initial : consistent (List.ofFn x ++ [false,true],0) (List.ofFn y ++ [false,true],0) :=
    ⟨le_rfl,fun _ => inputs_order xy⟩
  have result := run_consistent C.gates allowed initial
  refine ⟨result.1,?_⟩
  intro eq
  have order := (result.2 eq).2
  rw [run_wires,run_wires] at order
  exact order

theorem grade_fall {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool}
    (xy : x ≤ y) (i : ℕ)
    (before : (C.wires (List.ofFn x ++ [false,true])).getD i false = true)
    (after : (C.wires (List.ofFn y ++ [false,true])).getD i false = false) :
    grade C x < grade C y := by
  obtain ⟨order,read⟩ := grade_order basis xy
  refine lt_of_le_of_ne order ?_
  intro eq
  have impossible := read eq i
  rw [before,after] at impossible
  exact (by decide : ¬ (true ≤ false)) impossible

abbrev Reach {n m : ℕ} (P N : (Fin n → Bool) → Fin m → Prop) :
    ℕ → (Fin n → Bool) → Prop :=
  Nat.rec (motive := fun _ => (Fin n → Bool) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j)

theorem no_packing_of_taps {n m r : ℕ} {P N : (Fin n → Bool) → Fin m → Prop}
    {C : Circuit} (tap : Fin m → ℕ) (basis : FanInTwo C) (budget : notCount C ≤ r)
    (fits : ∀ x j,
      let w := (C.wires (List.ofFn x ++ [false,true])).getD (tap j) false
      (P x j → w = true) ∧ (N x j → w = false)) :
    ∀ x, ¬ Reach P N (2^r) x := by
  have lower : ∀ k x, Reach P N k x → k ≤ grade C x := by
    intro k
    induction k with
    | zero => intro x _; exact Nat.zero_le _
    | succ k ih =>
      intro x reached
      obtain ⟨u,v,j,history,uv,vx,positive,negative⟩ := reached
      have old := ih u history
      have middle := grade_fall basis uv (tap j) ((fits u j).1 positive) ((fits v j).2 negative)
      have last := (grade_order basis vx).1
      omega
  intro x found
  have high := lower _ x found
  have low := (grade_bound C x).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) budget)
  omega

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

def value (C : Circuit) (x : List Bool) (i : Nat) : Bool := (C.wires x).getD i false

def nextWire (n : Nat) (C : Circuit) : Nat := n + C.size

def emptyCircuit : Circuit := ⟨[], 0⟩

def appendGate (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], C.output⟩

def appendAnd (C : Circuit) (a b : Nat) : Circuit := appendGate C ⟨.and, [a,b]⟩

def appendOr (C : Circuit) (a b : Nat) : Circuit := appendGate C ⟨.or, [a,b]⟩

def appendNot (C : Circuit) (a : Nat) : Circuit := appendGate C ⟨.not, [a]⟩

def withOutput (C : Circuit) (o : Nat) : Circuit := ⟨C.gates, o⟩

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

private theorem fold_length (gates : List Gate) (x : List Bool) :
    (gates.foldl gateStep x).length = x.length + gates.length := by
  induction gates generalizing x with
  | nil => simp
  | cons g rest ih =>
    rw [List.foldl_cons,ih]
    simp [gateStep] <;> omega

private theorem fold_value (gates : List Gate) (x : List Bool) {i : Nat} (valid : i < x.length) :
    (gates.foldl gateStep x).getD i false = x.getD i false := by
  induction gates generalizing x with
  | nil => rfl
  | cons g rest ih =>
    have available : i < (gateStep x g).length := by simp [gateStep]; omega
    rw [List.foldl_cons,ih _ available]
    exact List.getD_append _ _ _ _ valid

@[local simp] theorem emptyCircuit_size : emptyCircuit.size = 0 := rfl

@[local simp] theorem emptyCircuit_notCount : notCount emptyCircuit = 0 := rfl

theorem emptyCircuit_fanInTwo : FanInTwo emptyCircuit := by
  simp [FanInTwo,emptyCircuit]

theorem emptyCircuit_readsBack (n : Nat) : ReadsBack n emptyCircuit := by
  simp [ReadsBack,emptyCircuit]

@[local simp] theorem withOutput_size (C : Circuit) (o : Nat) : (withOutput C o).size = C.size := rfl

@[local simp] theorem withOutput_output (C : Circuit) (o : Nat) : (withOutput C o).output = o := rfl

@[local simp] theorem withOutput_notCount (C : Circuit) (o : Nat) :
    notCount (withOutput C o) = notCount C := rfl

@[local simp] theorem withOutput_fanInTwo (C : Circuit) (o : Nat) :
    FanInTwo (withOutput C o) ↔ FanInTwo C := Iff.rfl

@[local simp] theorem withOutput_readsBack (n : Nat) (C : Circuit) (o : Nat) :
    ReadsBack n (withOutput C o) ↔ ReadsBack n C := Iff.rfl

@[local simp] theorem withOutput_value (C : Circuit) (o : Nat) (x : List Bool) (i : Nat) :
    value (withOutput C o) x i = value C x i := rfl

@[local simp] theorem withOutput_eval (C : Circuit) (o : Nat) (x : List Bool) :
    (withOutput C o).eval x = value C x o := rfl

theorem withOutput_valid {n : Nat} {C : Circuit} {o : Nat} (valid : o < nextWire n C) :
    (withOutput C o).output < n + (withOutput C o).size := valid

@[local simp] theorem appendGate_size (C : Circuit) (g : Gate) :
    (appendGate C g).size = C.size + 1 := by
  simp [appendGate,Circuit.size]

@[local simp] theorem appendGate_output (C : Circuit) (g : Gate) :
    (appendGate C g).output = C.output := rfl

theorem appendGate_prefix (C : Circuit) (g : Gate) : C.gates <+: (appendGate C g).gates :=
  ⟨[g],rfl⟩

@[local simp] theorem appendGate_notCount (C : Circuit) (g : Gate) :
    notCount (appendGate C g) = notCount C + (@ite ℕ (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not) 1 0) := by
  by_cases inv : g.op = .not <;> simp [notCount,appendGate,inv]

@[local simp] theorem nextWire_appendGate (n : Nat) (C : Circuit) (g : Gate) :
    nextWire n (appendGate C g) = nextWire n C + 1 := by
  simp [nextWire,Nat.add_assoc]

theorem appendGate_fanInTwo {C : Circuit} {g : Gate} (basis : FanInTwo C)
    (op : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (arity : g.inputs.length ≤ 2) : FanInTwo (appendGate C g) := by
  intro k hk
  rcases List.mem_append.mp hk with old | new
  · exact basis k old
  · have same : k = g := List.mem_singleton.mp new
    subst k
    exact ⟨op,arity⟩

theorem appendGate_readsBack {n : Nat} {C : Circuit} {g : Gate} (valid : ReadsBack n C)
    (inputs : ∀ i ∈ g.inputs, i < nextWire n C) : ReadsBack n (appendGate C g) := by
  intro j hj i hi
  change i ∈ ((C.gates ++ [g]).getD j ⟨.or, []⟩).inputs at hi
  by_cases old : j < C.gates.length
  · rw [List.getD_append _ _ _ _ old] at hi
    exact valid j old i hi
  · change j < (C.gates ++ [g]).length at hj
    have same : j = C.gates.length := by simp at hj; omega
    subst j
    rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
    exact inputs i (by simpa using hi)

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = nextWire x.length C := by
  rw [wires_eq]
  exact fold_length C.gates x

theorem value_input (C : Circuit) (x : List Bool) {i : Nat} (valid : i < x.length) :
    value C x i = x.getD i false := by
  rw [value,wires_eq]
  exact fold_value C.gates x valid

theorem nextWire_le_of_prefix {n : Nat} {C D : Circuit} (extension : C.gates <+: D.gates) :
    nextWire n C ≤ nextWire n D := Nat.add_le_add_left extension.length_le n

theorem value_of_prefix {C D : Circuit} (extension : C.gates <+: D.gates) {x : List Bool}
    {i : Nat} (valid : i < nextWire x.length C) : value D x i = value C x i := by
  obtain ⟨rest,appended⟩ := extension
  simp only [value,wires_eq,← appended,List.foldl_append]
  apply fold_value
  rw [fold_length]
  exact valid

theorem appendGate_wires (C : Circuit) (g : Gate) (x : List Bool) :
    (appendGate C g).wires x = C.wires x ++ [g.op.eval (g.inputs.map fun i => value C x i)] := by
  simp [appendGate,wires_eq,gateStep,value]

theorem appendGate_old {C : Circuit} {g : Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendGate C g) x i = value C x i :=
  value_of_prefix (appendGate_prefix C g) valid

theorem appendGate_new (C : Circuit) (g : Gate) (x : List Bool) :
    value (appendGate C g) x (nextWire x.length C) =
      g.op.eval (g.inputs.map fun i => value C x i) := by
  rw [value,appendGate_wires,← wires_length]
  simp [List.getD_eq_getElem?_getD]

@[local simp] theorem appendAnd_size (C : Circuit) (a b : Nat) :
    (appendAnd C a b).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendOr_size (C : Circuit) (a b : Nat) :
    (appendOr C a b).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendNot_size (C : Circuit) (a : Nat) :
    (appendNot C a).size = C.size + 1 := appendGate_size _ _

@[local simp] theorem appendAnd_notCount (C : Circuit) (a b : Nat) :
    notCount (appendAnd C a b) = notCount C := by simp [appendAnd]

@[local simp] theorem appendOr_notCount (C : Circuit) (a b : Nat) :
    notCount (appendOr C a b) = notCount C := by simp [appendOr]

@[local simp] theorem appendNot_notCount (C : Circuit) (a : Nat) :
    notCount (appendNot C a) = notCount C + 1 := by simp [appendNot]

theorem appendAnd_fanInTwo {C : Circuit} {a b : Nat} (basis : FanInTwo C) :
    FanInTwo (appendAnd C a b) := appendGate_fanInTwo (g := ⟨.and,[a,b]⟩) basis (by simp) (by simp)

theorem appendOr_fanInTwo {C : Circuit} {a b : Nat} (basis : FanInTwo C) :
    FanInTwo (appendOr C a b) := appendGate_fanInTwo (g := ⟨.or,[a,b]⟩) basis (by simp) (by simp)

theorem appendNot_fanInTwo {C : Circuit} {a : Nat} (basis : FanInTwo C) :
    FanInTwo (appendNot C a) := appendGate_fanInTwo (g := ⟨.not,[a]⟩) basis (by simp) (by simp)

theorem appendAnd_readsBack {n : Nat} {C : Circuit} {a b : Nat} (valid : ReadsBack n C)
    (left : a < nextWire n C) (right : b < nextWire n C) : ReadsBack n (appendAnd C a b) := by
  apply appendGate_readsBack (g := ⟨.and,[a,b]⟩) valid
  intro i member
  change i ∈ [a,b] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact left
  · exact right

theorem appendOr_readsBack {n : Nat} {C : Circuit} {a b : Nat} (valid : ReadsBack n C)
    (left : a < nextWire n C) (right : b < nextWire n C) : ReadsBack n (appendOr C a b) := by
  apply appendGate_readsBack (g := ⟨.or,[a,b]⟩) valid
  intro i member
  change i ∈ [a,b] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact left
  · exact right

theorem appendNot_readsBack {n : Nat} {C : Circuit} {a : Nat} (valid : ReadsBack n C)
    (input : a < nextWire n C) : ReadsBack n (appendNot C a) := by
  apply appendGate_readsBack (g := ⟨.not,[a]⟩) valid
  intro i member
  have same : i = a := List.mem_singleton.mp member
  subst i
  exact input

theorem appendAnd_new (C : Circuit) (x : List Bool) (a b : Nat) :
    value (appendAnd C a b) x (nextWire x.length C) = (value C x a && value C x b) := by
  simpa [appendAnd,GateOp.eval] using appendGate_new C ⟨.and,[a,b]⟩ x

theorem appendOr_new (C : Circuit) (x : List Bool) (a b : Nat) :
    value (appendOr C a b) x (nextWire x.length C) = (value C x a || value C x b) := by
  simpa [appendOr,GateOp.eval] using appendGate_new C ⟨.or,[a,b]⟩ x

theorem appendNot_new (C : Circuit) (x : List Bool) (a : Nat) :
    value (appendNot C a) x (nextWire x.length C) = !value C x a := by
  exact appendGate_new C ⟨.not,[a]⟩ x

section Fold

variable {α : Type}

def sfold (F : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun W g => W ++ [F W g]) init

theorem sfold_length (F : List α → Gate → α) (init : List α) (gs : List Gate) :
    (sfold F init gs).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [sfold]
  | cons g rest ih =>
    simp only [sfold, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

theorem sfold_old (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) {j : ℕ}
    (hj : j < init.length) : (sfold F init gs).getD j d = init.getD j d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g rest ih =>
    simp only [sfold, List.foldl_cons] at ih ⊢
    rw [ih (init ++ [F init g]) (by simp; omega)]
    exact List.getD_append _ _ _ _ hj

theorem sfold_append (F : List α → Gate → α) (init : List α) (gs1 gs2 : List Gate) :
    sfold F init (gs1 ++ gs2) = sfold F (sfold F init gs1) gs2 := by
  simp [sfold, List.foldl_append]

theorem sfold_at (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) (m : ℕ)
    (hm : m < gs.length) :
    (sfold F init gs).getD (init.length + m) d = F (sfold F init (gs.take m)) gs[m] := by
  have hsplit : gs.take m ++ (gs[m] :: gs.drop (m+1)) = gs := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hlen := sfold_length F init (gs.take m)
  rw [List.length_take, min_eq_left hm.le] at hlen
  conv_lhs => rw [← hsplit]
  rw [sfold_append]
  show (sfold F (sfold F init (gs.take m) ++ [F (sfold F init (gs.take m)) gs[m]])
    (gs.drop (m+1))).getD (init.length + m) d = _
  rw [sfold_old _ _ _ _ (by simp [hlen])]
  rw [List.getD_append_right _ _ _ _ (by rw [hlen])]
  simp [hlen]

theorem sfold_gate (F : List α → Gate → α) (d : α)
    (hloc : ∀ W1 W2 g, (∀ j ∈ g.inputs, W1.getD j d = W2.getD j d) → F W1 g = F W2 g)
    (init : List α) (gs : List Gate)
    (hreads : ∀ m (hm : m < gs.length), ∀ j ∈ gs[m].inputs, j < init.length + m)
    (m : ℕ) (hm : m < gs.length) :
    (sfold F init gs).getD (init.length + m) d = F (sfold F init gs) gs[m] := by
  rw [sfold_at F init gs d m hm]
  apply hloc
  intro j hj
  have hjl := hreads m hm j hj
  have hfull : sfold F init gs = sfold F (sfold F init (gs.take m)) (gs.drop m) := by
    rw [← sfold_append, List.take_append_drop]
  rw [hfull]
  exact (sfold_old F (sfold F init (gs.take m)) (gs.drop m) d
    (by rw [sfold_length, List.length_take, min_eq_left hm.le]; exact hjl)).symm

theorem sfold_beyond (F : List α → Gate → α) (init : List α) (gs : List Gate) (d : α) {j : ℕ}
    (hj : init.length + gs.length ≤ j) : (sfold F init gs).getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [sfold_length]; exact hj)]
  rfl

end Fold

def Fval (W : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => W.getD i false)

theorem Fval_loc (W1 W2 : List Bool) (g : Gate) (h : ∀ j ∈ g.inputs, W1.getD j false = W2.getD j false) :
    Fval W1 g = Fval W2 g := by
  unfold Fval
  congr 1
  exact List.map_congr_left h

theorem wires_sfold (C : Circuit) (x : List Bool) : C.wires x = sfold Fval x C.gates := rfl

theorem mem_foldl_union {β : Type} {inst : DecidableEq β} (W : List (Finset β)) (l : List ℕ) (base : Finset β) (z : β) :
    z ∈ l.foldl (fun acc j => acc ∪ W.getD j ∅) base ↔ z ∈ base ∨ ∃ j ∈ l, z ∈ W.getD j ∅ := by
  induction l generalizing base with
  | nil => simp
  | cons j rest ih =>
    rw [List.foldl_cons, ih, Finset.mem_union]
    constructor
    · rintro ((h | h) | ⟨j', hj', h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj', h⟩
    · rintro (h | ⟨j', hj', h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hj' with rfl | h2
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨j', h2, h⟩

noncomputable def Fpath (W : List (Finset (ℕ × ℕ))) (g : Gate) : Finset (ℕ × ℕ) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  (g.inputs.foldl (fun acc j => acc ∪ W.getD j ∅) ∅).image
    (fun z => if g.op = GateOp.and then (z.1+1,z.2) else (z.1,z.2+1))

noncomputable def seedsX {k : ℕ} (i : Fin k) : List (Finset (ℕ × ℕ)) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  List.ofFn (fun j : Fin k => if j=i then ({(0,0)} : Finset (ℕ × ℕ)) else ∅) ++ [∅,∅]

noncomputable def pathsX {k : ℕ} (i : Fin k) (D : Circuit) : Finset (ℕ × ℕ) :=
  (sfold Fpath (seedsX i) D.gates).getD D.output ∅

theorem Fpath_loc (W1 W2 : List (Finset (ℕ × ℕ))) (g : Gate)
    (h : ∀ j ∈ g.inputs, W1.getD j ∅ = W2.getD j ∅) : Fpath W1 g = Fpath W2 g := by
  unfold Fpath
  congr 1
  apply Finset.ext
  intro z
  rw [mem_foldl_union, mem_foldl_union]
  constructor
  · rintro (h1 | ⟨j, hj, h1⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, by rw [← h j hj]; exact h1⟩
  · rintro (h1 | ⟨j, hj, h1⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, by rw [h j hj]; exact h1⟩

theorem mem_Fpath_and (W : List (Finset (ℕ × ℕ))) (g : Gate) (hop : g.op = GateOp.and) (z : ℕ × ℕ) :
    z ∈ Fpath W g ↔ ∃ j ∈ g.inputs, ∃ z' ∈ W.getD j ∅, z = (z'.1+1, z'.2) := by
  unfold Fpath
  simp only [Finset.mem_image, mem_foldl_union, hop, if_true]
  constructor
  · rintro ⟨z', (h | ⟨j, hj, h⟩), rfl⟩
    · simp at h
    · exact ⟨j, hj, z', h, rfl⟩
  · rintro ⟨j, hj, z', h, rfl⟩
    exact ⟨z', Or.inr ⟨j, hj, h⟩, rfl⟩

theorem mem_Fpath_other (W : List (Finset (ℕ × ℕ))) (g : Gate) (hop : g.op ≠ GateOp.and) (z : ℕ × ℕ) :
    z ∈ Fpath W g ↔ ∃ j ∈ g.inputs, ∃ z' ∈ W.getD j ∅, z = (z'.1, z'.2+1) := by
  unfold Fpath
  simp only [Finset.mem_image, mem_foldl_union, hop, if_false]
  constructor
  · rintro ⟨z', (h | ⟨j, hj, h⟩), rfl⟩
    · simp at h
    · exact ⟨j, hj, z', h, rfl⟩
  · rintro ⟨j, hj, z', h, rfl⟩
    exact ⟨z', Or.inr ⟨j, hj, h⟩, rfl⟩

theorem seedsX_length {k : ℕ} (i : Fin k) : (seedsX i).length = k + 2 := by
  simp [seedsX]

theorem seedsX_self {k : ℕ} (i : Fin k) : ((0,0) : ℕ × ℕ) ∈ (seedsX i).getD i.val ∅ := by
  simp [seedsX, List.getD_eq_getElem?_getD, List.getElem?_append_left, i.isLt]

theorem seedsX_mem {k : ℕ} (i : Fin k) (j : ℕ) (z : ℕ × ℕ) (h : z ∈ (seedsX i).getD j ∅) :
    z = (0,0) := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hc : (seedsX i)[j]? with
  | none =>
    rw [hc] at h
    simp at h
  | some S =>
    rw [hc] at h
    have hS : S ∈ seedsX i := List.mem_of_getElem? hc
    simp only [Option.getD_some] at h
    unfold seedsX at hS
    simp only [List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hS
    rcases hS with ⟨j', rfl⟩ | rfl | rfl
    · split_ifs at h <;> simp_all
    · simp at h
    · simp at h

noncomputable def Ftime (c e : ℕ) (W : List ℕ) (g : Gate) : ℕ :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  if g.op = GateOp.not then ((g.inputs.head?.map (fun j => W.getD j 0)).getD 0)
    else g.inputs.foldl (fun v j => max v (W.getD j 0)) 0 + (if g.op = GateOp.and then c else e)

noncomputable def delayX (k c e : ℕ) (D : Circuit) : ℕ :=
  (sfold (Ftime c e) (List.replicate (k+2) 0) D.gates).getD D.output 0

theorem foldl_max_loc (W1 W2 : List ℕ) (l : List ℕ) (h : ∀ j ∈ l, W1.getD j 0 = W2.getD j 0) (b : ℕ) :
    l.foldl (fun v j => max v (W1.getD j 0)) b = l.foldl (fun v j => max v (W2.getD j 0)) b := by
  induction l generalizing b with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.foldl_cons]
    rw [h j (List.mem_cons_self ..)]
    exact ih (fun j' hj' => h j' (List.mem_cons_of_mem _ hj')) _

theorem le_foldl_max (W : List ℕ) (l : List ℕ) (b : ℕ) :
    b ≤ l.foldl (fun v j => max v (W.getD j 0)) b ∧
      ∀ j ∈ l, W.getD j 0 ≤ l.foldl (fun v j => max v (W.getD j 0)) b := by
  induction l generalizing b with
  | nil => simp
  | cons j rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (max b (W.getD j 0))
    refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
    intro j' hj'
    rcases List.mem_cons.1 hj' with rfl | h3
    · exact le_trans (le_max_right _ _) h1
    · exact h2 j' h3

theorem Ftime_loc (c e : ℕ) (W1 W2 : List ℕ) (g : Gate) (h : ∀ j ∈ g.inputs, W1.getD j 0 = W2.getD j 0) :
    Ftime c e W1 g = Ftime c e W2 g := by
  unfold Ftime
  rw [foldl_max_loc W1 W2 g.inputs h]
  congr 1
  cases hg : g.inputs with
  | nil => rfl
  | cons j rest =>
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    exact h j (by rw [hg]; exact List.mem_cons_self ..)

theorem Ftime_and (c e : ℕ) (W : List ℕ) (g : Gate) (hop : g.op = GateOp.and) :
    Ftime c e W g = g.inputs.foldl (fun v j => max v (W.getD j 0)) 0 + c := by
  unfold Ftime
  simp [hop]

theorem Ftime_or (c e : ℕ) (W : List ℕ) (g : Gate) (hop : g.op = GateOp.or) :
    Ftime c e W g = g.inputs.foldl (fun v j => max v (W.getD j 0)) 0 + e := by
  unfold Ftime
  simp [hop]

theorem prefix_mono {n : ℕ} {C : Circuit} (basis : FanInTwo C) (hn : notCount C = 0)
    {x y : Fin n → Bool} (hxy : x ≤ y) (i : ℕ) :
    (C.wires (List.ofFn x ++ [false,true])).getD i false ≤
      (C.wires (List.ofFn y ++ [false,true])).getD i false := by
  have h1 := grade_bound C x
  have h2 := grade_bound C y
  rw [hn] at h1 h2
  simp only [pow_zero, Nat.lt_one_iff] at h1 h2
  exact (grade_order basis hxy).2 (by rw [h1, h2]) i

theorem bool_le_false {b : Bool} (h : b ≤ false) : b = false := by
  cases b
  · rfl
  · exact absurd ((bool_order _ _).1 h rfl) (by decide)

theorem bool_true_le {b : Bool} (h : true ≤ b) : b = true := (bool_order _ _).1 h rfl

theorem no_not_gate {D : Circuit} (hn : notCount D = 0) : ∀ g ∈ D.gates, g.op ≠ GateOp.not := by
  intro g hg hop
  have h0 : (D.gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)) = [] :=
    List.eq_nil_of_length_eq_zero hn
  have := List.filter_eq_nil_iff.1 h0 g hg
  simp [hop] at this

theorem reads_get {n : ℕ} {D : Circuit} (hr : ReadsBack n D) :
    ∀ m (hm : m < D.gates.length), ∀ j ∈ D.gates[m].inputs, j < n + m := by
  intro m hm j hj
  apply hr m hm j
  show j ∈ (D.gates.getD m ⟨GateOp.or, []⟩).inputs
  rw [List.getD_eq_getElem _ _ hm]
  exact hj

section Core

variable {k : ℕ} [dk : DecidableEq (Fin k)]

def inpX (Y : Finset (Fin k)) : List Bool := List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true]

theorem inpX_length (Y : Finset (Fin k)) : (inpX Y).length = k + 2 := by simp [inpX]

theorem inpX_lt (Y : Finset (Fin k)) (w : ℕ) (h : w < k) :
    (inpX Y).getD w false = decide ((⟨w, h⟩ : Fin k) ∈ Y) := by
  have inside : w < (List.ofFn (fun j : Fin k => decide (j ∈ Y))).length := by simpa using h
  simp only [inpX, List.getD_eq_getElem?_getD, List.getElem?_append_left inside]
  simp [List.getElem?_ofFn, h]

theorem inpX_k (Y : Finset (Fin k)) : (inpX Y).getD k false = false := by
  simp [inpX, List.getD_eq_getElem?_getD]

theorem inpX_k1 (Y : Finset (Fin k)) : (inpX Y).getD (k+1) false = true := by
  have outside : (List.ofFn (fun j : Fin k => decide (j ∈ Y))).length ≤ k+1 := by simp
  simp [inpX, List.getD_eq_getElem?_getD, List.getElem?_append_right outside]

def valX (D : Circuit) (w : ℕ) (Y : Finset (Fin k)) : Bool := (D.wires (inpX Y)).getD w false

theorem valX_mono {D : Circuit} (hf : FanInTwo D) (hn : notCount D = 0) (w : ℕ) {Y Y' : Finset (Fin k)}
    (h : Y ⊆ Y') : valX D w Y ≤ valX D w Y' := by
  apply prefix_mono hf hn (x := fun j => decide (j ∈ Y)) (y := fun j => decide (j ∈ Y'))
  intro j
  apply (bool_order _ _).2
  intro hy
  simp only [decide_eq_true_eq] at hy ⊢
  exact h hy

theorem card_union_sdiff_le (Y1 Y2 A : Finset (Fin k)) :
    ((Y1 ∪ Y2) \ A).card ≤ (Y1 \ A).card + (Y2 \ A).card := by
  have hsub : (Y1 ∪ Y2) \ A ⊆ (Y1 \ A) ∪ (Y2 \ A) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem card_sdiff_inter_le (B Y1 Y2 : Finset (Fin k)) :
    (B \ (Y1 ∩ Y2)).card ≤ (B \ Y1).card + (B \ Y2).card := by
  have hsub : B \ (Y1 ∩ Y2) ⊆ (B \ Y1) ∪ (B \ Y2) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hx ⊢
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem core (A B : Finset (Fin k)) (hAB : A ⊆ B) (D : Circuit) (hf : FanInTwo D)
    (hr : ReadsBack (k+2) D) (hn : notCount D = 0) :
    ∀ w, w < k + 2 + D.size → ∀ P Q : ℕ, 1 ≤ P → 1 ≤ Q →
      (∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (Y \ A).card < P → valX D w Y = false) →
      (∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (B \ Y).card < Q → valX D w Y = true) →
      ∃ i ∈ B \ A, ∃ uv ∈ (sfold Fpath (seedsX i) D.gates).getD w ∅,
        P ≤ 2^uv.1 ∧ Q ≤ 2^uv.2 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw P Q hP hQ hfalse htrue
  have hAA : (A \ A).card < P := by simp; omega
  have hBB : (B \ B).card < Q := by simp; omega
  by_cases hwk : w < k
  · let j : Fin k := ⟨w, hwk⟩
    have hval : ∀ Y : Finset (Fin k), valX D w Y = decide (j ∈ Y) := by
      intro Y
      unfold valX
      rw [wires_sfold, sfold_old _ _ _ _ (by rw [inpX_length]; omega), inpX_lt Y w hwk]
    have hjB : j ∈ B := by
      by_contra hjB
      have := htrue B hAB (subset_refl _) hBB
      rw [hval] at this
      exact hjB (of_decide_eq_true this)
    have hjA : j ∉ A := by
      intro hjA
      have := hfalse A (subset_refl _) hAB hAA
      rw [hval] at this
      exact absurd hjA (of_decide_eq_false this)
    have hP1 : P ≤ 1 := by
      by_contra hP1
      have hs : insert j A \ A = {j} := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact h1
          · exact absurd h1 h2
        · rintro rfl
          exact ⟨Or.inl rfl, hjA⟩
      have := hfalse (insert j A) (Finset.subset_insert _ _) (Finset.insert_subset hjB hAB)
        (by rw [hs, Finset.card_singleton]; omega)
      rw [hval] at this
      exact absurd (Finset.mem_insert_self j A) (of_decide_eq_false this)
    have hQ1 : Q ≤ 1 := by
      by_contra hQ1
      have hs : B \ B.erase j = {j} := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩
          by_contra h3
          exact h2 ⟨h3, h1⟩
        · rintro rfl
          exact ⟨hjB, fun h => h.1 rfl⟩
      have hAe : A ⊆ B.erase j := by
        intro x hx
        exact Finset.mem_erase.2 ⟨fun h => hjA (h ▸ hx), hAB hx⟩
      have := htrue (B.erase j) hAe (Finset.erase_subset _ _) (by rw [hs, Finset.card_singleton]; omega)
      rw [hval] at this
      exact absurd (of_decide_eq_true this) (Finset.notMem_erase j B)
    refine ⟨j, Finset.mem_sdiff.2 ⟨hjB, hjA⟩, (0,0), ?_, by simpa using hP1, by simpa using hQ1⟩
    rw [sfold_old _ _ _ _ (by rw [seedsX_length]; omega)]
    exact seedsX_self j
  by_cases hwk2 : w < k + 2
  · exfalso
    have hval : ∀ Y : Finset (Fin k), valX D w Y = (inpX Y).getD w false := by
      intro Y
      unfold valX
      rw [wires_sfold, sfold_old _ _ _ _ (by rw [inpX_length]; omega)]
    by_cases h1 : w = k + 1
    · have := hfalse A (subset_refl _) hAB hAA
      rw [hval, h1, inpX_k1] at this
      exact absurd this (by decide)
    · have h2 : w = k := by omega
      have := htrue B hAB (subset_refl _) hBB
      rw [hval, h2, inpX_k] at this
      exact absurd this (by decide)
  obtain ⟨m, rfl⟩ : ∃ m, w = k + 2 + m := ⟨w - (k+2), by omega⟩
  have hm : m < D.gates.length := by
    have : D.size = D.gates.length := rfl
    omega
  have hreads := reads_get hr
  have hgin : ∀ j ∈ D.gates[m].inputs, j < k + 2 + m := hreads m hm
  have hgval : ∀ Y : Finset (Fin k), valX D (k+2+m) Y = Fval (D.wires (inpX Y)) D.gates[m] := by
    intro Y
    unfold valX
    rw [wires_sfold]
    have := sfold_gate Fval false Fval_loc (inpX Y) D.gates
      (fun m' hm' j hj => by rw [inpX_length]; exact hreads m' hm' j hj) m hm
    rw [inpX_length] at this
    exact this
  have hgpath : ∀ i : Fin k, (sfold Fpath (seedsX i) D.gates).getD (k+2+m) ∅ =
      Fpath (sfold Fpath (seedsX i) D.gates) D.gates[m] := by
    intro i
    have := sfold_gate Fpath ∅ Fpath_loc (seedsX i) D.gates
      (fun m' hm' j hj => by rw [seedsX_length]; exact hreads m' hm' j hj) m hm
    rw [seedsX_length] at this
    exact this
  have hgshape := hf D.gates[m] (List.getElem_mem hm)
  have hgnot := no_not_gate hn D.gates[m] (List.getElem_mem hm)
  obtain ⟨hop, hlen⟩ := hgshape
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have hop2 : D.gates[m].op = GateOp.and ∨ D.gates[m].op = GateOp.or := by
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hgnot
  have hvY : ∀ j ∈ D.gates[m].inputs, ∀ Y : Finset (Fin k), (D.wires (inpX Y)).getD j false = valX D j Y :=
    fun _ _ _ => rfl
  have hPh : 1 ≤ (P+1)/2 := by omega
  have hQh : 1 ≤ (Q+1)/2 := by omega
  rcases hop2 with hand | hor
  ·
    have hev : ∀ Y : Finset (Fin k), valX D (k+2+m) Y = (D.gates[m].inputs.map fun j => valX D j Y).all id := by
      intro Y
      rw [hgval, Fval, hand]
      rfl
    have hpath : ∀ (i : Fin k) (u : ℕ), u ∈ D.gates[m].inputs → ∀ z ∈ (sfold Fpath (seedsX i) D.gates).getD u ∅,
        (z.1+1, z.2) ∈ (sfold Fpath (seedsX i) D.gates).getD (k+2+m) ∅ := by
      intro i u hu z hz
      rw [hgpath, mem_Fpath_and _ _ hand]
      exact ⟨u, hu, z, hz, rfl⟩
    have hT : ∀ u ∈ D.gates[m].inputs, ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (B \ Y).card < Q → valX D u Y = true := by
      intro u hu Y h1 h2 h3
      have := htrue Y h1 h2 h3
      rw [hev, List.all_eq_true] at this
      exact this _ (List.mem_map.2 ⟨u, hu, rfl⟩)
    have lift : ∀ u ∈ D.gates[m].inputs, ∀ P', 1 ≤ P' → P ≤ 2*P' →
        (∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (Y \ A).card < P' → valX D u Y = false) →
        ∃ i ∈ B \ A, ∃ uv ∈ (sfold Fpath (seedsX i) D.gates).getD (k+2+m) ∅,
          P ≤ 2^uv.1 ∧ Q ≤ 2^uv.2 := by
      intro u hu P' hP' hPP hF
      obtain ⟨i, hi, z, hz, h1, h2⟩ := ih u (hgin u hu) (by have := hgin u hu; omega) P' Q hP' hQ hF (hT u hu)
      refine ⟨i, hi, (z.1+1, z.2), hpath i u hu z hz, ?_, h2⟩
      rw [pow_succ]
      omega
    match hgi : D.gates[m].inputs, hlen with
    | [], _ =>
      exfalso
      have := hfalse A (subset_refl _) hAB hAA
      rw [hev, hgi] at this
      simp at this
    | [u], _ =>
      have hu : u ∈ D.gates[m].inputs := by rw [hgi]; simp
      apply lift u hu P hP (by omega)
      intro Y h1 h2 h3
      have := hfalse Y h1 h2 h3
      rw [hev, hgi] at this
      simpa using this
    | [u1, u2], _ =>
      have hu1 : u1 ∈ D.gates[m].inputs := by rw [hgi]; simp
      have hu2 : u2 ∈ D.gates[m].inputs := by rw [hgi]; simp
      by_cases hc1 : ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (Y \ A).card < (P+1)/2 → valX D u1 Y = false
      · exact lift u1 hu1 _ hPh (by omega) hc1
      by_cases hc2 : ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (Y \ A).card < (P+1)/2 → valX D u2 Y = false
      · exact lift u2 hu2 _ hPh (by omega) hc2
      exfalso
      push_neg at hc1 hc2
      obtain ⟨Y1, a1, b1, c1, d1⟩ := hc1
      obtain ⟨Y2, a2, b2, c2, d2⟩ := hc2
      have hY : ((Y1 ∪ Y2) \ A).card < P := by
        have := card_union_sdiff_le Y1 Y2 A
        omega
      have := hfalse (Y1 ∪ Y2) (a1.trans Finset.subset_union_left) (Finset.union_subset b1 b2) hY
      rw [hev, hgi] at this
      have e1 := bool_true_le ((show true = valX D u1 Y1 by simpa using d1.symm) ▸
        valX_mono hf hn u1 (Finset.subset_union_left (s₂ := Y2)))
      have e2 := bool_true_le ((show true = valX D u2 Y2 by simpa using d2.symm) ▸
        valX_mono hf hn u2 (Finset.subset_union_right (s₁ := Y1)))
      simp [e1, e2] at this
    | _ :: _ :: _ :: _, hl =>
      simp at hl
  ·
    have hand' : D.gates[m].op ≠ GateOp.and := by rw [hor]; intro h; cases h
    have hev : ∀ Y : Finset (Fin k), valX D (k+2+m) Y = (D.gates[m].inputs.map fun j => valX D j Y).any id := by
      intro Y
      rw [hgval, Fval, hor]
      rfl
    have hpath : ∀ (i : Fin k) (u : ℕ), u ∈ D.gates[m].inputs → ∀ z ∈ (sfold Fpath (seedsX i) D.gates).getD u ∅,
        (z.1, z.2+1) ∈ (sfold Fpath (seedsX i) D.gates).getD (k+2+m) ∅ := by
      intro i u hu z hz
      rw [hgpath, mem_Fpath_other _ _ hand']
      exact ⟨u, hu, z, hz, rfl⟩
    have hF : ∀ u ∈ D.gates[m].inputs, ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (Y \ A).card < P → valX D u Y = false := by
      intro u hu Y h1 h2 h3
      have := hfalse Y h1 h2 h3
      rw [hev] at this
      have h4 := List.any_eq_false.1 this
      have h5 := h4 _ (List.mem_map.2 ⟨u, hu, rfl⟩)
      simpa using h5
    have lift : ∀ u ∈ D.gates[m].inputs, ∀ Q', 1 ≤ Q' → Q ≤ 2*Q' →
        (∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (B \ Y).card < Q' → valX D u Y = true) →
        ∃ i ∈ B \ A, ∃ uv ∈ (sfold Fpath (seedsX i) D.gates).getD (k+2+m) ∅,
          P ≤ 2^uv.1 ∧ Q ≤ 2^uv.2 := by
      intro u hu Q' hQ' hQQ hT
      obtain ⟨i, hi, z, hz, h1, h2⟩ := ih u (hgin u hu) (by have := hgin u hu; omega) P Q' hP hQ' (hF u hu) hT
      refine ⟨i, hi, (z.1, z.2+1), hpath i u hu z hz, h1, ?_⟩
      show Q ≤ 2^(z.2+1)
      rw [pow_succ]
      omega
    match hgi : D.gates[m].inputs, hlen with
    | [], _ =>
      exfalso
      have := htrue B hAB (subset_refl _) hBB
      rw [hev, hgi] at this
      simp at this
    | [u], _ =>
      have hu : u ∈ D.gates[m].inputs := by rw [hgi]; simp
      apply lift u hu Q hQ (by omega)
      intro Y h1 h2 h3
      have := htrue Y h1 h2 h3
      rw [hev, hgi] at this
      simpa using this
    | [u1, u2], _ =>
      have hu1 : u1 ∈ D.gates[m].inputs := by rw [hgi]; simp
      have hu2 : u2 ∈ D.gates[m].inputs := by rw [hgi]; simp
      by_cases hc1 : ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (B \ Y).card < (Q+1)/2 → valX D u1 Y = true
      · exact lift u1 hu1 _ hQh (by omega) hc1
      by_cases hc2 : ∀ Y : Finset (Fin k), A ⊆ Y → Y ⊆ B → (B \ Y).card < (Q+1)/2 → valX D u2 Y = true
      · exact lift u2 hu2 _ hQh (by omega) hc2
      exfalso
      push_neg at hc1 hc2
      obtain ⟨Y1, a1, b1, c1, d1⟩ := hc1
      obtain ⟨Y2, a2, b2, c2, d2⟩ := hc2
      have hY : (B \ (Y1 ∩ Y2)).card < Q := by
        have := card_sdiff_inter_le B Y1 Y2
        omega
      have := htrue (Y1 ∩ Y2) (Finset.subset_inter a1 a2) (Finset.inter_subset_left.trans b1) hY
      rw [hev, hgi] at this
      have e1 := bool_le_false ((show valX D u1 Y1 = false by simpa using d1) ▸
        valX_mono hf hn u1 (Finset.inter_subset_left (s₂ := Y2)))
      have e2 := bool_le_false ((show valX D u2 Y2 = false by simpa using d2) ▸
        valX_mono hf hn u2 (Finset.inter_subset_right (s₁ := Y1)))
      simp [e1, e2] at this
    | _ :: _ :: _ :: _, hl =>
      simp at hl

theorem delay_ge (D : Circuit) (hr : ReadsBack (k+2) D) (hn : notCount D = 0) (hf : FanInTwo D)
    (c e : ℕ) (i : Fin k) : ∀ w, ∀ z ∈ (sfold Fpath (seedsX i) D.gates).getD w ∅,
      c*z.1 + e*z.2 ≤ (sfold (Ftime c e) (List.replicate (k+2) 0) D.gates).getD w 0 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro z hz
  by_cases hw : w < k + 2
  · rw [sfold_old _ _ _ _ (by rw [seedsX_length]; exact hw)] at hz
    have := seedsX_mem i w z hz
    subst this
    simp
  by_cases hw2 : w < k + 2 + D.gates.length
  · obtain ⟨m, rfl⟩ : ∃ m, w = k + 2 + m := ⟨w - (k+2), by omega⟩
    have hm : m < D.gates.length := by omega
    have hreads := reads_get hr
    have hgp := sfold_gate Fpath ∅ Fpath_loc (seedsX i) D.gates
      (fun m' hm' j hj => by rw [seedsX_length]; exact hreads m' hm' j hj) m hm
    rw [seedsX_length] at hgp
    have hgt := sfold_gate (Ftime c e) 0 (Ftime_loc c e) (List.replicate (k+2) 0) D.gates
      (fun m' hm' j hj => by rw [List.length_replicate]; exact hreads m' hm' j hj) m hm
    rw [List.length_replicate] at hgt
    rw [hgt]
    rw [hgp] at hz
    obtain ⟨hop, _⟩ := hf D.gates[m] (List.getElem_mem hm)
    have hgnot := no_not_gate hn D.gates[m] (List.getElem_mem hm)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hand | hor | hnot
    · rw [mem_Fpath_and _ _ hand] at hz
      obtain ⟨j, hj, z', hz', rfl⟩ := hz
      have h1 := ih j (by have := hreads m hm j hj; omega) z' hz'
      have h2 := (le_foldl_max (sfold (Ftime c e) (List.replicate (k+2) 0) D.gates) D.gates[m].inputs 0).2 j hj
      rw [Ftime_and _ _ _ _ hand]
      nlinarith
    · rw [mem_Fpath_other _ _ (by rw [hor]; intro h; cases h)] at hz
      obtain ⟨j, hj, z', hz', rfl⟩ := hz
      have h1 := ih j (by have := hreads m hm j hj; omega) z' hz'
      have h2 := (le_foldl_max (sfold (Ftime c e) (List.replicate (k+2) 0) D.gates) D.gates[m].inputs 0).2 j hj
      rw [Ftime_or _ _ _ _ hor]
      nlinarith
    · exact absurd hnot hgnot
  · rw [sfold_beyond _ _ _ _ (by rw [seedsX_length]; omega)] at hz
    simp at hz

end Core

section Build

variable {α : Type}

def semC (F : List α → Gate → α) (init : List α) (d : α) (C : Circuit) (w : ℕ) : α :=
  (sfold F init C.gates).getD w d

theorem semC_prefix (F : List α → Gate → α) (init : List α) (d : α) {C C' : Circuit}
    (hp : C.gates <+: C'.gates) {w : ℕ} (hw : w < init.length + C.size) :
    semC F init d C' w = semC F init d C w := by
  obtain ⟨rest, hr⟩ := hp
  unfold semC
  rw [← hr, sfold_append]
  exact sfold_old _ _ _ _ (by rw [sfold_length]; exact hw)

theorem semC_append (F : List α → Gate → α) (init : List α) (d : α) (C : Circuit) (g : Gate) :
    semC F init d (appendGate C g) (init.length + C.size) = F (sfold F init C.gates) g := by
  unfold semC appendGate
  simp only
  rw [sfold_append]
  have hl : init.length + C.size = (sfold F init C.gates).length := by
    rw [sfold_length]; rfl
  rw [hl]
  simp [sfold, List.getD_eq_getElem?_getD]

theorem semC_empty (F : List α → Gate → α) (init : List α) (d : α) (w : ℕ) :
    semC F init d emptyCircuit w = init.getD w d := rfl

def tfold (f : α → α → α) (v : ℕ → α) : ℕ → List ℕ → α
  | 0, L => v (L.headD 0)
  | h+1, L => if L.length ≤ 2^h then tfold f v h L else
      f (tfold f v h (L.take (2^h))) (tfold f v h (L.drop (2^h)))

theorem headD_mem {L : List ℕ} (h : L ≠ []) : L.headD 0 ∈ L := by
  cases L with
  | nil => exact absurd rfl h
  | cons x rest => simp

theorem split_ne {L : List ℕ} (h : ℕ) (hl : ¬ L.length ≤ 2^h) :
    L.take (2^h) ≠ [] ∧ L.drop (2^h) ≠ [] := by
  have hp : 0 < 2^h := pow_pos (by norm_num) h
  constructor
  · intro he
    rw [List.take_eq_nil_iff] at he
    rcases he with he | he
    · omega
    · rw [he] at hl; simp at hl
  · intro he
    rw [List.drop_eq_nil_iff] at he
    exact hl he

theorem split_len {L : List ℕ} (h : ℕ) (hl : L.length ≤ 2^(h+1)) :
    (L.take (2^h)).length ≤ 2^h ∧ (L.drop (2^h)).length ≤ 2^h := by
  rw [pow_succ] at hl
  simp only [List.length_take, List.length_drop]
  constructor
  · exact min_le_left _ _
  · omega

theorem tfold_congr (f : α → α → α) (h : ℕ) : ∀ (L : List ℕ) (v v' : ℕ → α), L ≠ [] →
    (∀ j ∈ L, v j = v' j) → tfold f v h L = tfold f v' h L := by
  induction h with
  | zero =>
    intro L v v' hne hv
    exact hv _ (headD_mem hne)
  | succ h ih =>
    intro L v v' hne hv
    unfold tfold
    split_ifs with hl
    · exact ih L v v' hne hv
    · obtain ⟨h1, h2⟩ := split_ne h hl
      rw [ih _ v v' h1 (fun j hj => hv j (List.mem_of_mem_take hj)),
        ih _ v v' h2 (fun j hj => hv j (List.mem_of_mem_drop hj))]

theorem tfold_le (c : ℕ) (h : ℕ) : ∀ (L : List ℕ) (v : ℕ → ℕ) (M : ℕ), L ≠ [] →
    (∀ j ∈ L, v j ≤ M) → tfold (fun x y => max x y + c) v h L ≤ M + h * c := by
  induction h with
  | zero =>
    intro L v M hne hv
    simpa [tfold] using hv _ (headD_mem hne)
  | succ h ih =>
    intro L v M hne hv
    unfold tfold
    split_ifs with hl
    · have := ih L v M hne hv
      nlinarith
    · obtain ⟨h1, h2⟩ := split_ne h hl
      have a1 := ih _ v M h1 (fun j hj => hv j (List.mem_of_mem_take hj))
      have a2 := ih _ v M h2 (fun j hj => hv j (List.mem_of_mem_drop hj))
      have : max (tfold (fun x y => max x y + c) v h (L.take (2^h)))
          (tfold (fun x y => max x y + c) v h (L.drop (2^h))) ≤ M + h * c := max_le a1 a2
      nlinarith

theorem tfold_all (h : ℕ) : ∀ (L : List ℕ) (v : ℕ → Bool), L ≠ [] → L.length ≤ 2^h →
    tfold (fun x y => x && y) v h L = L.all v := by
  induction h with
  | zero =>
    intro L v hne hl
    match L, hne, hl with
    | [x], _, _ => simp [tfold]
    | [], hne, _ => exact absurd rfl hne
    | _ :: _ :: _, _, hl => simp at hl
  | succ h ih =>
    intro L v hne hl
    unfold tfold
    split_ifs with hl2
    · exact ih L v hne hl2
    · obtain ⟨h1, h2⟩ := split_ne h hl2
      obtain ⟨l1, l2⟩ := split_len h hl
      rw [ih _ v h1 l1, ih _ v h2 l2]
      conv_rhs => rw [← List.take_append_drop (2^h) L]
      rw [List.all_append]

theorem tfold_any (h : ℕ) : ∀ (L : List ℕ) (v : ℕ → Bool), L ≠ [] → L.length ≤ 2^h →
    tfold (fun x y => x || y) v h L = L.any v := by
  induction h with
  | zero =>
    intro L v hne hl
    match L, hne, hl with
    | [x], _, _ => simp [tfold]
    | [], hne, _ => exact absurd rfl hne
    | _ :: _ :: _, _, hl => simp at hl
  | succ h ih =>
    intro L v hne hl
    unfold tfold
    split_ifs with hl2
    · exact ih L v hne hl2
    · obtain ⟨h1, h2⟩ := split_ne h hl2
      obtain ⟨l1, l2⟩ := split_len h hl
      rw [ih _ v h1 l1, ih _ v h2 l2]
      conv_rhs => rw [← List.take_append_drop (2^h) L]
      rw [List.any_append]

def bt (op : GateOp) (n : ℕ) : ℕ → Circuit → List ℕ → Circuit × ℕ
  | 0, C, L => (C, L.headD 0)
  | h+1, C, L => if L.length ≤ 2^h then bt op n h C L else
      ((appendGate (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).1
        ⟨op, [(bt op n h C (L.take (2^h))).2, (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).2]⟩),
        n + (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).1.size)

def BinForm (op : GateOp) (F : List α → Gate → α) (d : α) (f : α → α → α) : Prop :=
  ∀ W a b, F W ⟨op, [a, b]⟩ = f (W.getD a d) (W.getD b d)

theorem bt_spec (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (n : ℕ) (h : ℕ) :
    ∀ (C : Circuit) (L : List ℕ), L ≠ [] → L.length ≤ 2^h → (∀ j ∈ L, j < n + C.size) →
      C.gates <+: (bt op n h C L).1.gates ∧ (bt op n h C L).1.output = C.output ∧
      (bt op n h C L).2 < n + (bt op n h C L).1.size ∧
      (FanInTwo C → FanInTwo (bt op n h C L).1) ∧ (ReadsBack n C → ReadsBack n (bt op n h C L).1) ∧
      notCount (bt op n h C L).1 = notCount C ∧
      (∀ (β : Type) (F : List β → Gate → β) (init : List β) (d : β) (f : β → β → β),
        init.length = n → BinForm op F d f →
        semC F init d (bt op n h C L).1 (bt op n h C L).2 = tfold f (semC F init d C) h L) := by
  induction h with
  | zero =>
    intro C L hne hl hj
    refine ⟨List.prefix_refl _, rfl, hj _ (headD_mem hne), id, id, rfl, ?_⟩
    intro β F init d f _ _
    rfl
  | succ h ih =>
    intro C L hne hl hj
    by_cases hl2 : L.length ≤ 2^h
    · have e : bt op n (h+1) C L = bt op n h C L := by
        simp only [bt, if_pos hl2]
      rw [e]
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := ih C L hne hl2 hj
      refine ⟨a1, a2, a3, a4, a5, a6, ?_⟩
      intro β F init d f hi hb
      rw [a7 β F init d f hi hb]
      simp only [tfold, if_pos hl2]
    · have e : bt op n (h+1) C L = ((appendGate (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).1
        ⟨op, [(bt op n h C (L.take (2^h))).2, (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).2]⟩),
        n + (bt op n h (bt op n h C (L.take (2^h))).1 (L.drop (2^h))).1.size) := by
        simp only [bt, if_neg hl2]
      rw [e]
      obtain ⟨h1, h2⟩ := split_ne h hl2
      obtain ⟨l1, l2⟩ := split_len h hl
      obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := ih C (L.take (2^h)) h1 l1
        (fun j hj' => hj j (List.mem_of_mem_take hj'))
      set C1 := (bt op n h C (L.take (2^h))).1 with hC1
      set w1 := (bt op n h C (L.take (2^h))).2 with hw1
      have hs1 : C.size ≤ C1.size := b1.length_le
      obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := ih C1 (L.drop (2^h)) h2 l2
        (fun j hj' => by have := hj j (List.mem_of_mem_drop hj'); omega)
      set C2 := (bt op n h C1 (L.drop (2^h))).1 with hC2
      set w2 := (bt op n h C1 (L.drop (2^h))).2 with hw2
      have hs2 : C1.size ≤ C2.size := c1.length_le
      have hopset : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
        rcases hop with rfl | rfl <;> simp
      have hnot : op ≠ GateOp.not := by
        rcases hop with rfl | rfl <;> (intro hh; cases hh)
      refine ⟨b1.trans (c1.trans (appendGate_prefix _ _)), by rw [appendGate_output, c2, b2], ?_,
        fun hf => appendGate_fanInTwo (c4 (b4 hf)) hopset (by simp), ?_, ?_, ?_⟩
      · rw [appendGate_size]; omega
      · intro hr
        apply appendGate_readsBack (c5 (b5 hr))
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        unfold nextWire
        rcases hi with rfl | rfl
        · omega
        · exact c3
      · rw [appendGate_notCount, c6, b6]
        simp [hnot]
      · intro β F init d f hi hb
        have := semC_append F init d C2 ⟨op, [w1, w2]⟩
        rw [hi] at this
        rw [this, hb]
        show f (semC F init d C2 w1) (semC F init d C2 w2) = _
        rw [semC_prefix F init d c1 (by rw [hi]; exact b3), b7 β F init d f hi hb,
          c7 β F init d f hi hb,
          tfold_congr f h _ (semC F init d C1) (semC F init d C) h2
            (fun j hj' => semC_prefix F init d b1 (by rw [hi]; exact hj j (List.mem_of_mem_drop hj')))]
        simp only [tfold, if_neg hl2]

def seqB (n hf : ℕ) : Circuit → List (List ℕ) → Circuit × List ℕ
  | C, [] => (C, [])
  | C, G :: Gs => ((seqB n hf (bt GateOp.and n hf C G).1 Gs).1,
      (bt GateOp.and n hf C G).2 :: (seqB n hf (bt GateOp.and n hf C G).1 Gs).2)

theorem seqB_spec (n hf : ℕ) : ∀ (Gs : List (List ℕ)) (C : Circuit),
    (∀ G ∈ Gs, G ≠ [] ∧ G.length ≤ 2^hf ∧ ∀ j ∈ G, j < n + C.size) →
      C.gates <+: (seqB n hf C Gs).1.gates ∧ (seqB n hf C Gs).1.output = C.output ∧
      (seqB n hf C Gs).2.length = Gs.length ∧
      (∀ o ∈ (seqB n hf C Gs).2, o < n + (seqB n hf C Gs).1.size) ∧
      (FanInTwo C → FanInTwo (seqB n hf C Gs).1) ∧ (ReadsBack n C → ReadsBack n (seqB n hf C Gs).1) ∧
      notCount (seqB n hf C Gs).1 = notCount C ∧
      (∀ (β : Type) (F : List β → Gate → β) (init : List β) (d : β) (f : β → β → β),
        init.length = n → BinForm GateOp.and F d f →
        (∀ o ∈ (seqB n hf C Gs).2, ∃ G ∈ Gs, semC F init d (seqB n hf C Gs).1 o = tfold f (semC F init d C) hf G) ∧
        (∀ G ∈ Gs, ∃ o ∈ (seqB n hf C Gs).2, semC F init d (seqB n hf C Gs).1 o = tfold f (semC F init d C) hf G)) := by
  intro Gs
  induction Gs with
  | nil =>
    intro C _
    refine ⟨List.prefix_refl _, rfl, rfl, by simp [seqB], id, id, rfl, ?_⟩
    intro β F init d f _ _
    simp [seqB]
  | cons G Gs ih =>
    intro C hG
    obtain ⟨g1, g2, g3⟩ := hG G (List.mem_cons_self ..)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := bt_spec GateOp.and (Or.inl rfl) n hf C G g1 g2 g3
    set C1 := (bt GateOp.and n hf C G).1 with hC1
    set w1 := (bt GateOp.and n hf C G).2 with hw1
    have hs1 : C.size ≤ C1.size := b1.length_le
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := ih C1 (fun G' hG' => by
      obtain ⟨x1, x2, x3⟩ := hG G' (List.mem_cons_of_mem _ hG')
      exact ⟨x1, x2, fun j hj => by have := x3 j hj; omega⟩)
    have e : seqB n hf C (G :: Gs) = ((seqB n hf C1 Gs).1, w1 :: (seqB n hf C1 Gs).2) := rfl
    rw [e]
    have hs2 : C1.size ≤ (seqB n hf C1 Gs).1.size := c1.length_le
    refine ⟨b1.trans c1, by rw [c2, b2], by simp [c3], ?_, fun hf' => c5 (b4 hf'), fun hr => c6 (b5 hr),
      by rw [c7, b6], ?_⟩
    · intro o ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · show w1 < n + (seqB n hf C1 Gs).1.size
        omega
      · exact c4 o ho
    · intro β F init d f hi hb
      obtain ⟨d1, d2⟩ := c8 β F init d f hi hb
      have conv : ∀ G' ∈ Gs, tfold f (semC F init d C1) hf G' = tfold f (semC F init d C) hf G' := by
        intro G' hG'
        obtain ⟨x1, _, x3⟩ := hG G' (List.mem_cons_of_mem _ hG')
        exact tfold_congr f hf G' _ _ x1 (fun j hj => semC_prefix F init d b1 (by rw [hi]; exact x3 j hj))
      have first : semC F init d (seqB n hf C1 Gs).1 w1 = tfold f (semC F init d C) hf G := by
        rw [semC_prefix F init d c1 (by rw [hi]; exact b3), b7 β F init d f hi hb]
      constructor
      · intro o ho
        simp only [List.mem_cons] at ho
        rcases ho with rfl | ho
        · exact ⟨G, List.mem_cons_self .., first⟩
        · obtain ⟨G', hG', e'⟩ := d1 o ho
          exact ⟨G', List.mem_cons_of_mem _ hG', by rw [e', conv G' hG']⟩
      · intro G' hG'
        simp only [List.mem_cons] at hG'
        rcases hG' with rfl | hG'
        · exact ⟨w1, List.mem_cons_self .., first⟩
        · obtain ⟨o, ho, e'⟩ := d2 G' hG'
          exact ⟨o, List.mem_cons_of_mem _ ho, by rw [e', conv G' hG']⟩

end Build

theorem inpX_fin {k : ℕ} [DecidableEq (Fin k)] (Y : Finset (Fin k)) (x : Fin k) :
    (inpX Y).getD x.val false = decide (x ∈ Y) := inpX_lt Y x.val x.isLt

section Final

variable {k : ℕ}

def grp (lt : List (Fin k)) (f i : ℕ) : List (Fin k) := (lt.drop (i*(f+1))).take (f+1)

theorem idx_inj {i i' t t' f : ℕ} (ht : t < f+1) (ht' : t' < f+1) (h : i*(f+1)+t = i'*(f+1)+t') :
    i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · have h1 : (i+1)*(f+1) ≤ i'*(f+1) := Nat.mul_le_mul (by omega) (le_refl _)
    have h2 : (i+1)*(f+1) = i*(f+1) + (f+1) := by ring
    omega
  · exact heq
  · have h1 : (i'+1)*(f+1) ≤ i*(f+1) := Nat.mul_le_mul (by omega) (le_refl _)
    have h2 : (i'+1)*(f+1) = i'*(f+1) + (f+1) := by ring
    omega

theorem grp_length {lt : List (Fin k)} {a f i : ℕ} (hlen : (a+1)*(f+1) ≤ lt.length) (hi : i < a+1) :
    (grp lt f i).length = f+1 := by
  unfold grp
  rw [List.length_take, List.length_drop]
  have h1 : (i+1)*(f+1) ≤ (a+1)*(f+1) := Nat.mul_le_mul (by omega) (le_refl _)
  have h2 : (i+1)*(f+1) = i*(f+1) + (f+1) := by ring
  omega

theorem grp_nodup {lt : List (Fin k)} (hnd : lt.Nodup) (f i : ℕ) : (grp lt f i).Nodup :=
  hnd.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))

theorem grp_sub {lt : List (Fin k)} {f i : ℕ} {x : Fin k} (hx : x ∈ grp lt f i) : x ∈ lt :=
  List.mem_of_mem_drop (List.mem_of_mem_take hx)

theorem grp_index {lt : List (Fin k)} {f i : ℕ} {x : Fin k} (hx : x ∈ grp lt f i) :
    ∃ t, t < f+1 ∧ ∃ hh : i*(f+1)+t < lt.length, lt[i*(f+1)+t] = x := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hx
  have ht' := ht
  simp only [grp, List.length_take, List.length_drop] at ht'
  have h1 : t < f+1 := by omega
  have h2 : i*(f+1)+t < lt.length := by omega
  refine ⟨t, h1, h2, ?_⟩
  simp [grp]

theorem grp_disj {lt : List (Fin k)} (hnd : lt.Nodup) {f i i' : ℕ} {x : Fin k} (hx : x ∈ grp lt f i)
    (hx' : x ∈ grp lt f i') : i = i' := by
  obtain ⟨t, ht, hh, rfl⟩ := grp_index hx
  obtain ⟨t', ht', hh', he⟩ := grp_index hx'
  have := (List.Nodup.getElem_inj_iff hnd).1 he
  exact (idx_inj ht' ht this).symm

theorem comb_false [dk : DecidableEq (Fin k)] {lt : List (Fin k)} {A B Y : Finset (Fin k)} {a f : ℕ}
    (hnd : lt.Nodup) (hH : ∀ x ∈ lt, x ∈ B \ A) (hlen : (a+1)*(f+1) ≤ lt.length)
    (hcard : (Y \ A).card ≤ f) {i : ℕ} (hi : i < a+1) : ∃ x ∈ grp lt f i, x ∉ Y := by
  by_contra hc
  push_neg at hc
  have hsub : (grp lt f i).toFinset ⊆ Y \ A := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_sdiff.2 ⟨hc x hx, (Finset.mem_sdiff.1 (hH x (grp_sub hx))).2⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (grp_nodup hnd f i), grp_length hlen hi] at this
  omega

theorem comb_true [dk : DecidableEq (Fin k)] {lt : List (Fin k)} {A B Y : Finset (Fin k)} {a f : ℕ}
    (hnd : lt.Nodup) (hH : ∀ x ∈ lt, x ∈ B \ A) (hlen : (a+1)*(f+1) ≤ lt.length)
    (hcard : (B \ Y).card ≤ a) : ∃ i, i < a+1 ∧ ∀ x ∈ grp lt f i, x ∈ Y := by
  by_contra hc
  push_neg at hc
  have hpos : 0 < lt.length := by
    have : 0 < (a+1)*(f+1) := Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos f)
    omega
  haveI : Inhabited (Fin k) := ⟨lt[0]⟩
  choose! φ hφ1 hφ2 using hc
  have := Finset.card_le_card_of_injOn (s := Finset.range (a+1)) (t := B \ Y) φ
    (by
      intro i hi
      have hi' : i < a+1 := by simpa using hi
      have hm := hH _ (grp_sub (hφ1 i hi'))
      exact Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hm).1, hφ2 i hi'⟩)
    (by
      intro i hi i' hi' he
      have h1 : i < a+1 := by simpa using hi
      have h2 : i' < a+1 := by simpa using hi'
      have hx := hφ1 i h1
      have hx' := hφ1 i' h2
      rw [he] at hx
      exact grp_disj hnd hx hx')
  rw [Finset.card_range] at this
  omega

def groupsN (lt : List (Fin k)) (a f : ℕ) : List (List ℕ) :=
  (List.range (a+1)).map (fun i => (grp lt f i).map Fin.val)

def mainC (lt : List (Fin k)) (a f : ℕ) : Circuit :=
  withOutput (bt GateOp.or (k+2) (Nat.clog 2 (a+1))
      (seqB (k+2) (Nat.clog 2 (f+1)) emptyCircuit (groupsN lt a f)).1
      (seqB (k+2) (Nat.clog 2 (f+1)) emptyCircuit (groupsN lt a f)).2).1
    (bt GateOp.or (k+2) (Nat.clog 2 (a+1))
      (seqB (k+2) (Nat.clog 2 (f+1)) emptyCircuit (groupsN lt a f)).1
      (seqB (k+2) (Nat.clog 2 (f+1)) emptyCircuit (groupsN lt a f)).2).2

theorem mainC_spec [dk : DecidableEq (Fin k)] {lt : List (Fin k)} {a f : ℕ}
    (hlen : (a+1)*(f+1) ≤ lt.length) (c e : ℕ) :
    FanInTwo (mainC lt a f) ∧ ReadsBack (k+2) (mainC lt a f) ∧
    (mainC lt a f).output < k+2+(mainC lt a f).size ∧ notCount (mainC lt a f) = 0 ∧
    (∀ Y : Finset (Fin k), valX (mainC lt a f) (mainC lt a f).output Y = true ↔
      ∃ i, i < a+1 ∧ ∀ x ∈ grp lt f i, x ∈ Y) ∧
    delayX k c e (mainC lt a f) ≤ c * Nat.clog 2 (f+1) + e * Nat.clog 2 (a+1) := by
  have hb : (1:ℕ) < 2 := by norm_num
  have hG : ∀ G ∈ groupsN lt a f, G ≠ [] ∧ G.length ≤ 2^(Nat.clog 2 (f+1)) ∧
      ∀ j ∈ G, j < (k+2) + emptyCircuit.size := by
    intro G hG
    simp only [groupsN, List.mem_map, List.mem_range] at hG
    obtain ⟨i, hi, rfl⟩ := hG
    have hl := grp_length hlen hi
    refine ⟨?_, ?_, ?_⟩
    · intro he
      have := congrArg List.length he
      simp [hl] at this
    · rw [List.length_map, hl]
      exact Nat.le_pow_clog hb _
    · intro j hj
      simp only [List.mem_map] at hj
      obtain ⟨x, _, rfl⟩ := hj
      have := x.isLt
      show x.val < k + 2 + 0
      omega
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ :=
    seqB_spec (k+2) (Nat.clog 2 (f+1)) (groupsN lt a f) emptyCircuit hG
  unfold mainC
  set S := seqB (k+2) (Nat.clog 2 (f+1)) emptyCircuit (groupsN lt a f) with hS
  have hlenS : S.2.length = a+1 := by rw [m3]; simp [groupsN]
  have hneS : S.2 ≠ [] := by
    intro he
    rw [he] at hlenS
    simp at hlenS
  have hle2 : S.2.length ≤ 2^(Nat.clog 2 (a+1)) := by rw [hlenS]; exact Nat.le_pow_clog hb _
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ :=
    bt_spec GateOp.or (Or.inr rfl) (k+2) (Nat.clog 2 (a+1)) S.1 S.2 hneS hle2 m4
  set T := bt GateOp.or (k+2) (Nat.clog 2 (a+1)) S.1 S.2 with hT
  refine ⟨t4 (m5 emptyCircuit_fanInTwo), t5 (m6 (emptyCircuit_readsBack _)), t3, ?_, ?_, ?_⟩
  · show notCount T.1 = 0
    rw [t6, m7]
    rfl
  · intro Y
    have bo : BinForm GateOp.or Fval false (fun x y => x || y) := by
      unfold BinForm
      intro W a b
      simp [Fval, GateOp.eval]
    have ba : BinForm GateOp.and Fval false (fun x y => x && y) := by
      unfold BinForm
      intro W a b
      simp [Fval, GateOp.eval]
    have e1 : valX (withOutput T.1 T.2) (withOutput T.1 T.2).output Y =
        semC Fval (inpX Y) false T.1 T.2 := rfl
    rw [e1, t7 Bool Fval (inpX Y) false _ (inpX_length Y) bo, tfold_any _ _ _ hneS hle2,
      List.any_eq_true]
    obtain ⟨d1, d2⟩ := m8 Bool Fval (inpX Y) false _ (inpX_length Y) ba
    have hgrp : ∀ G ∈ groupsN lt a f, tfold (fun x y => x && y) (semC Fval (inpX Y) false emptyCircuit)
        (Nat.clog 2 (f+1)) G = G.all (fun j => (inpX Y).getD j false) := by
      intro G hG'
      obtain ⟨x1, x2, _⟩ := hG G hG'
      rw [tfold_all _ _ _ x1 x2]
      rfl
    constructor
    · rintro ⟨o, ho, hv⟩
      obtain ⟨G, hG', he⟩ := d1 o ho
      rw [he, hgrp G hG'] at hv
      simp only [groupsN, List.mem_map, List.mem_range] at hG'
      obtain ⟨i, hi, rfl⟩ := hG'
      refine ⟨i, hi, ?_⟩
      intro x hx
      have h5 : (inpX Y).getD x.val false = true := List.all_eq_true.1 hv x.val (List.mem_map.2 ⟨x, hx, rfl⟩)
      rw [inpX_fin] at h5
      exact of_decide_eq_true h5
    · rintro ⟨i, hi, hall⟩
      have hG' : (grp lt f i).map Fin.val ∈ groupsN lt a f := by
        simp only [groupsN, List.mem_map, List.mem_range]
        exact ⟨i, hi, rfl⟩
      obtain ⟨o, ho, he⟩ := d2 _ hG'
      refine ⟨o, ho, ?_⟩
      rw [he, hgrp _ hG', List.all_eq_true]
      intro j hj
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hj
      show (inpX Y).getD x.val false = true
      rw [inpX_fin]
      exact decide_eq_true (hall x hx)
  · have bat : BinForm GateOp.and (Ftime c e) 0 (fun x y => max x y + c) := by
      unfold BinForm
      intro W a b
      rw [Ftime_and _ _ _ _ rfl]
      simp
    have bot : BinForm GateOp.or (Ftime c e) 0 (fun x y => max x y + e) := by
      unfold BinForm
      intro W a b
      rw [Ftime_or _ _ _ _ rfl]
      simp
    have e1 : delayX k c e (withOutput T.1 T.2) = semC (Ftime c e) (List.replicate (k+2) 0) 0 T.1 T.2 := rfl
    rw [e1, t7 ℕ (Ftime c e) _ 0 _ (by simp) bot]
    obtain ⟨d1, _⟩ := m8 ℕ (Ftime c e) (List.replicate (k+2) 0) 0 _ (by simp) bat
    have hb1 : ∀ o ∈ S.2, semC (Ftime c e) (List.replicate (k+2) 0) 0 S.1 o ≤ Nat.clog 2 (f+1) * c := by
      intro o ho
      obtain ⟨G, hG', he⟩ := d1 o ho
      rw [he]
      obtain ⟨x1, _, _⟩ := hG G hG'
      have := tfold_le c (Nat.clog 2 (f+1)) G (semC (Ftime c e) (List.replicate (k+2) 0) 0 emptyCircuit) 0 x1
        (fun j _ => by
          rw [semC_empty, List.getD_eq_getElem?_getD, List.getElem?_replicate]
          split_ifs <;> simp)
      simpa using this
    have h3 := tfold_le e (Nat.clog 2 (a+1)) S.2 _ _ hneS hb1
    have h4 : Nat.clog 2 (f+1) * c + Nat.clog 2 (a+1) * e = c * Nat.clog 2 (f+1) + e * Nat.clog 2 (a+1) := by
      ring
    omega

end Final

end Build1470


namespace Formula1468

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive SForm (k : Nat) where
  | const (b : Bool)
  | lit (j : Fin k) (pol : Bool)
  | and (l r : SForm k)
  | or (l r : SForm k)

def SForm.eval {k : Nat} (Y : Finset (Fin k)) : SForm k → Bool
  | .const b => b
  | .lit j pol => if pol then decide (j ∈ Y) else !decide (j ∈ Y)
  | .and l r => l.eval Y && r.eval Y
  | .or l r => l.eval Y || r.eval Y

def SForm.neg {k : Nat} : SForm k → SForm k
  | .const b => .const (!b)
  | .lit j pol => .lit j (!pol)
  | .and l r => .or l.neg r.neg
  | .or l r => .and l.neg r.neg

def SForm.posCount {k : Nat} (J : Finset (Fin k)) : SForm k → Nat
  | .const _ => 0
  | .lit j pol => if pol = true ∧ j ∈ J then 1 else 0
  | .and l r => l.posCount J + r.posCount J
  | .or l r => l.posCount J + r.posCount J

def SForm.negCount {k : Nat} (J : Finset (Fin k)) : SForm k → Nat
  | .const _ => 0
  | .lit j pol => if pol = false ∧ j ∈ J then 1 else 0
  | .and l r => l.negCount J + r.negCount J
  | .or l r => l.negCount J + r.negCount J

def SForm.posVars {k : Nat} : SForm k → Finset (Fin k)
  | .const _ => ∅
  | .lit j pol => if pol then {j} else ∅
  | .and l r => l.posVars ∪ r.posVars
  | .or l r => l.posVars ∪ r.posVars

def SForm.negVars {k : Nat} : SForm k → Finset (Fin k)
  | .const _ => ∅
  | .lit j pol => if pol then ∅ else {j}
  | .and l r => l.negVars ∪ r.negVars
  | .or l r => l.negVars ∪ r.negVars

def SForm.andConf {k : Nat} : SForm k → Finset (Fin k)
  | .const _ => ∅
  | .lit _ _ => ∅
  | .and l r => l.andConf ∪ r.andConf ∪ ((l.posVars ∩ r.negVars) ∪ (l.negVars ∩ r.posVars))
  | .or l r => l.andConf ∪ r.andConf

def SForm.orConf {k : Nat} : SForm k → Finset (Fin k)
  | .const _ => ∅
  | .lit _ _ => ∅
  | .and l r => l.orConf ∪ r.orConf
  | .or l r => l.orConf ∪ r.orConf ∪ ((l.posVars ∩ r.negVars) ∪ (l.negVars ∩ r.posVars))

def SForm.markTuple {k : Nat} (F : SForm k) :
    (Finset (Fin k) × Finset (Fin k)) × (Finset (Fin k) × Finset (Fin k)) :=
  ((F.posVars, F.negVars), (F.andConf, F.orConf))

lemma SForm.eval_neg {k : Nat} (Y : Finset (Fin k)) (F : SForm k) :
    F.neg.eval Y = !(F.eval Y) := by
  induction F with
  | const b => rfl
  | lit j pol => cases pol <;> simp [SForm.neg, SForm.eval]
  | and l r ihl ihr => simp [SForm.neg, SForm.eval, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.eval, ihl, ihr]

lemma SForm.posCount_neg {k : Nat} (J : Finset (Fin k)) (F : SForm k) :
    F.neg.posCount J = F.negCount J := by
  induction F with
  | const b => rfl
  | lit j pol => cases pol <;> simp [SForm.neg, SForm.posCount, SForm.negCount]
  | and l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]

lemma SForm.negCount_neg {k : Nat} (J : Finset (Fin k)) (F : SForm k) :
    F.neg.negCount J = F.posCount J := by
  induction F with
  | const b => rfl
  | lit j pol => cases pol <;> simp [SForm.neg, SForm.posCount, SForm.negCount]
  | and l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]

lemma SForm.posVars_neg {k : Nat} (F : SForm k) : F.neg.posVars = F.negVars := by
  induction F with
  | const _ => rfl
  | lit j pol => cases pol <;> rfl
  | and l r ihl ihr => simp [SForm.neg, SForm.posVars, SForm.negVars, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.posVars, SForm.negVars, ihl, ihr]

lemma SForm.negVars_neg {k : Nat} (F : SForm k) : F.neg.negVars = F.posVars := by
  induction F with
  | const _ => rfl
  | lit j pol => cases pol <;> rfl
  | and l r ihl ihr => simp [SForm.neg, SForm.posVars, SForm.negVars, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.posVars, SForm.negVars, ihl, ihr]

lemma SForm.andConf_neg {k : Nat} (F : SForm k) : F.neg.andConf = F.orConf := by
  induction F with
  | const _ => rfl
  | lit _ _ => rfl
  | and l r ihl ihr => simp [SForm.neg, SForm.andConf, SForm.orConf, ihl, ihr]
  | or l r ihl ihr =>
    simp only [SForm.neg, SForm.andConf, SForm.orConf, ihl, ihr, SForm.posVars_neg, SForm.negVars_neg]
    ext x; simp; tauto

lemma SForm.orConf_neg {k : Nat} (F : SForm k) : F.neg.orConf = F.andConf := by
  induction F with
  | const _ => rfl
  | lit _ _ => rfl
  | and l r ihl ihr =>
    simp only [SForm.neg, SForm.andConf, SForm.orConf, ihl, ihr, SForm.posVars_neg, SForm.negVars_neg]
    ext x; simp; tauto
  | or l r ihl ihr => simp [SForm.neg, SForm.andConf, SForm.orConf, ihl, ihr]

lemma SForm.andConf_sub_posVars {k : Nat} (F : SForm k) : F.andConf ⊆ F.posVars := by
  induction F with
  | const _ => exact Finset.Subset.rfl
  | lit _ _ => exact Finset.empty_subset _
  | and l r ihl ihr =>
    intro x hx
    simp only [SForm.andConf, SForm.posVars, Finset.mem_union, Finset.mem_inter] at hx ⊢
    rcases hx with (h | h) | (⟨h, _⟩ | ⟨_, h⟩)
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)
    · exact Or.inl h
    · exact Or.inr h
  | or l r ihl ihr =>
    intro x hx
    simp only [SForm.andConf, SForm.posVars, Finset.mem_union] at hx ⊢
    rcases hx with h | h
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)

lemma SForm.orConf_sub_posVars {k : Nat} (F : SForm k) : F.orConf ⊆ F.posVars := by
  induction F with
  | const _ => exact Finset.Subset.rfl
  | lit _ _ => exact Finset.empty_subset _
  | and l r ihl ihr =>
    intro x hx
    simp only [SForm.orConf, SForm.posVars, Finset.mem_union] at hx ⊢
    rcases hx with h | h
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)
  | or l r ihl ihr =>
    intro x hx
    simp only [SForm.orConf, SForm.posVars, Finset.mem_union, Finset.mem_inter] at hx ⊢
    rcases hx with (h | h) | (⟨h, _⟩ | ⟨_, h⟩)
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)
    · exact Or.inl h
    · exact Or.inr h

lemma SForm.posCount_add_disjoint {k : Nat} {A B : Finset (Fin k)} (hAB : Disjoint A B) (F : SForm k) :
    F.posCount (A ∪ B) = F.posCount A + F.posCount B := by
  induction F with
  | const _ => rfl
  | lit j pol =>
    cases pol with
    | false => simp [SForm.posCount]
    | true =>
      by_cases hA : j ∈ A
      · have hB : j ∉ B := Finset.disjoint_left.mp hAB hA
        simp [SForm.posCount, hA, hB]
      · by_cases hB : j ∈ B <;> simp [SForm.posCount, hA, hB]
  | and l r ihl ihr => simp only [SForm.posCount, ihl, ihr]; omega
  | or l r ihl ihr => simp only [SForm.posCount, ihl, ihr]; omega

lemma SForm.posCount_ge_card_inter_posVars {k : Nat} (K : Finset (Fin k)) (F : SForm k) :
    (K ∩ F.posVars).card ≤ F.posCount K := by
  induction F with
  | const _ => simp [SForm.posVars, SForm.posCount]
  | lit j pol =>
    cases pol with
    | false => simp [SForm.posVars, SForm.posCount]
    | true =>
      by_cases hj : j ∈ K
      · have heq : K ∩ {j} = {j} := by ext x; simp [hj]
        simp [SForm.posVars, SForm.posCount, heq, hj]
      · have heq : K ∩ {j} = ∅ := by ext x; simp; intro h1 h2; subst h2; exact hj h1
        simp [SForm.posVars, SForm.posCount, heq, hj]
  | and l r ihl ihr =>
    simp only [SForm.posVars, SForm.posCount, Finset.inter_union_distrib_left]
    calc (K ∩ l.posVars ∪ K ∩ r.posVars).card
        ≤ (K ∩ l.posVars).card + (K ∩ r.posVars).card := Finset.card_union_le _ _
      _ ≤ l.posCount K + r.posCount K := Nat.add_le_add ihl ihr
  | or l r ihl ihr =>
    simp only [SForm.posVars, SForm.posCount, Finset.inter_union_distrib_left]
    calc (K ∩ l.posVars ∪ K ∩ r.posVars).card
        ≤ (K ∩ l.posVars).card + (K ∩ r.posVars).card := Finset.card_union_le _ _
      _ ≤ l.posCount K + r.posCount K := Nat.add_le_add ihl ihr

def stepForm {k : Nat} (fs : List (SForm k)) (g : Gate) : SForm k :=
  match g.op, g.inputs with
  | .not, [] => .const true
  | .not, a :: _ => (fs.getD a (.const false)).neg
  | .and, [] => .const true
  | .and, [a] => fs.getD a (.const false)
  | .and, a :: b :: _ => .and (fs.getD a (.const false)) (fs.getD b (.const false))
  | .or, [] => .const false
  | .or, [a] => fs.getD a (.const false)
  | .or, a :: b :: _ => .or (fs.getD a (.const false)) (fs.getD b (.const false))
  | _, _ => .const false

lemma getD_append_singleton {α : Type*} (l : List α) (x d : α) (i : Nat) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  simp only [List.getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have hnone : ([x] : List α)[i - l.length]? = none :=
      List.getElem?_eq_none (by simp; omega)
    rw [hnone]; rfl

lemma mark_singleton_and {α : Type*} [DecidableEq α] (a b c d : Finset α) :
    ((a, b), (c, d)) = ((a ∪ ∅, b ∪ ∅), ((c ∪ ∅) ∪ ((a ∩ ∅) ∪ (b ∩ ∅)), d ∪ ∅)) := by
  simp

lemma mark_singleton_or {α : Type*} [DecidableEq α] (a b c d : Finset α) :
    ((a, b), (c, d)) = ((a ∪ ∅, b ∪ ∅), (c ∪ ∅, (d ∪ ∅) ∪ ((a ∩ ∅) ∪ (b ∩ ∅)))) := by
  simp

def canonical {k : Nat} (D : Circuit) : SForm k :=
  (D.gates.foldl (fun fs g=>fs++[stepForm fs g])
    (List.ofFn (fun j : Fin k=>SForm.lit j true)++[.const false,.const true])).getD D.output (.const false)

lemma canonical_spec {k : Nat} (D : Circuit) (hfit : FanInTwo D) :
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    let F := canonical (k:=k) D;
      (∀ Y : Finset (Fin k),
        F.eval Y = (D.wires (List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false, true])).getD D.output false) ∧
      (∀ J : Finset (Fin k),
        F.posCount J =
          ((D.gates.foldl (fun (zs : List (Nat × Nat)) g =>
            let ab := g.inputs.foldl (fun (acc : Nat × Nat) j =>
              let z := zs.getD j (0, 0)
              (acc.1 + z.1, acc.2 + z.2)) (0, 0)
            let h := (g.inputs.head?.map (fun j => zs.getD j (0, 0))).getD (0, 0)
            zs ++ [if g.op = GateOp.not then (h.2, h.1) else ab])
            (List.ofFn (fun j : Fin k => ((if j ∈ J then 1 else 0, 0) : Nat × Nat)) ++ [(0, 0), (0, 0)])).getD D.output (0, 0)).1) ∧
      F.markTuple =
        (let V := Finset (Fin k)
         let Z : (V × V) × (V × V) := ((∅, ∅), (∅, ∅))
         let xs := List.ofFn (fun j : Fin k => ((({j}, ∅), (∅, ∅)) : (V × V) × (V × V))) ++ [Z, Z]
         let ws := D.gates.foldl (fun (ts : List ((V × V) × (V × V))) g =>
           let a := (g.inputs.head?.map (fun j => ts.getD j Z)).getD Z
           let b := (g.inputs[1]?.map (fun j => ts.getD j Z)).getD Z
           let cross := (a.1.1 ∩ b.1.2) ∪ (a.1.2 ∩ b.1.1)
           let u := a.2.1 ∪ b.2.1
           let v := a.2.2 ∪ b.2.2
           ts ++ [if g.op = GateOp.not then ((a.1.2, a.1.1), (a.2.2, a.2.1))
             else ((a.1.1 ∪ b.1.1, a.1.2 ∪ b.1.2),
               if g.op = GateOp.and then (u ∪ cross, v) else (u, v ∪ cross))]) xs
         ws.getD D.output Z) := by
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let V := Finset (Fin k)
  let Z : (V × V) × (V × V) := ((∅, ∅), (∅, ∅))
  let stepW : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let stepC : List (Nat × Nat) → Gate → List (Nat × Nat) := fun zs g =>
    let ab := g.inputs.foldl (fun (acc : Nat × Nat) j =>
      let z := zs.getD j (0, 0)
      (acc.1 + z.1, acc.2 + z.2)) (0, 0)
    let h := (g.inputs.head?.map (fun j => zs.getD j (0, 0))).getD (0, 0)
    zs ++ [if g.op = GateOp.not then (h.2, h.1) else ab]
  let stepM : List ((V × V) × (V × V)) → Gate → List ((V × V) × (V × V)) := fun ts g =>
    let a := (g.inputs.head?.map (fun j => ts.getD j Z)).getD Z
    let b := (g.inputs[1]?.map (fun j => ts.getD j Z)).getD Z
    let cross := (a.1.1 ∩ b.1.2) ∪ (a.1.2 ∩ b.1.1)
    let u := a.2.1 ∪ b.2.1
    let v := a.2.2 ∪ b.2.2
    ts ++ [if g.op = GateOp.not then ((a.1.2, a.1.1), (a.2.2, a.2.1))
      else ((a.1.1 ∪ b.1.1, a.1.2 ∪ b.1.2),
        if g.op = GateOp.and then (u ∪ cross, v) else (u, v ∪ cross))]
  let stepF : List (SForm k) → Gate → List (SForm k) := fun fs g =>
    fs ++ [stepForm fs g]
  have hgen : ∀ (gs : List Gate) (fs : List (SForm k))
      (zs : Finset (Fin k) → List (Nat × Nat))
      (ws : Finset (Fin k) → List Bool)
      (ts : List ((V × V) × (V × V))),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ J, fs.length = (zs J).length) →
      (∀ Y, fs.length = (ws Y).length) →
      fs.length = ts.length →
      (∀ Y i, (fs.getD i (.const false)).eval Y = (ws Y).getD i false) →
      (∀ J i, (fs.getD i (.const false)).posCount J = ((zs J).getD i (0, 0)).1 ∧
              (fs.getD i (.const false)).negCount J = ((zs J).getD i (0, 0)).2) →
      (∀ i, (fs.getD i (.const false)).markTuple = ts.getD i Z) →
      let fs' := gs.foldl stepF fs
      let ts' := gs.foldl stepM ts
      (∀ Y i, (fs'.getD i (.const false)).eval Y = (gs.foldl stepW (ws Y)).getD i false) ∧
      (∀ J i, (fs'.getD i (.const false)).posCount J = ((gs.foldl stepC (zs J)).getD i (0, 0)).1 ∧
              (fs'.getD i (.const false)).negCount J = ((gs.foldl stepC (zs J)).getD i (0, 0)).2) ∧
      (∀ i, (fs'.getD i (.const false)).markTuple = ts'.getD i Z) := by
    intro gs
    induction gs with
    | nil =>
      intro fs zs ws ts _ _ _ _ hev hcnt hmk
      exact ⟨hev, hcnt, hmk⟩
    | cons g rest ih =>
      intro fs zs ws ts hgs hlenZ hlenW hlenT hev hcnt hmk
      simp only [List.foldl_cons]
      have hg := hgs g (by simp)
      have hrest : ∀ g' ∈ rest, (g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (by simp [hg'])
      have hstep_ev : ∀ Y, (stepForm fs g).eval Y = g.op.eval (g.inputs.map fun i => (ws Y).getD i false) := by
        intro Y
        rcases hg.1 with hop | hop | hop
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, GateOp.eval, SForm.eval]
          · simp only [stepForm, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
              List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact hev Y a
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, GateOp.eval, SForm.eval, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [hev Y a, hev Y b]
            | cons d e =>
              have hlen := hg.2
              rw [hin] at hlen
              simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, GateOp.eval, SForm.eval]
          · simp only [stepForm, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact hev Y a
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, GateOp.eval, SForm.eval, List.map_cons, List.map_nil,
                List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [hev Y a, hev Y b]
            | cons d e =>
              have hlen := hg.2
              rw [hin] at hlen
              simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, t⟩
          · simp [stepForm, hop, hin, GateOp.eval, SForm.eval]
          · simp only [stepForm, hop, hin, GateOp.eval, SForm.eval_neg, List.map_cons, List.headD_cons]
            rw [hev Y a]
      have hstep_cnt : ∀ J,
          (stepForm fs g).posCount J =
            (if g.op = GateOp.not then
              ((g.inputs.head?.map (fun j => (zs J).getD j (0, 0))).getD (0, 0)).2
            else
              (g.inputs.foldl (fun (acc : Nat × Nat) j =>
                let z := (zs J).getD j (0, 0); (acc.1 + z.1, acc.2 + z.2)) (0, 0)).1) ∧
          (stepForm fs g).negCount J =
            (if g.op = GateOp.not then
              ((g.inputs.head?.map (fun j => (zs J).getD j (0, 0))).getD (0, 0)).1
            else
              (g.inputs.foldl (fun (acc : Nat × Nat) j =>
                let z := (zs J).getD j (0, 0); (acc.1 + z.1, acc.2 + z.2)) (0, 0)).2) := by
        intro J
        rcases hg.1 with hop | hop | hop
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, SForm.posCount, SForm.negCount]
          · simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.foldl_cons, List.foldl_nil,
              Nat.zero_add]
            exact hcnt J a
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.foldl_cons, List.foldl_nil,
                Nat.zero_add, SForm.posCount, SForm.negCount]
              exact ⟨by rw [(hcnt J a).1, (hcnt J b).1], by rw [(hcnt J a).2, (hcnt J b).2]⟩
            | cons d e =>
              have hlen := hg.2; rw [hin] at hlen; simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, SForm.posCount, SForm.negCount]
          · simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.foldl_cons, List.foldl_nil,
              Nat.zero_add]
            exact hcnt J a
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.foldl_cons, List.foldl_nil,
                Nat.zero_add, SForm.posCount, SForm.negCount]
              exact ⟨by rw [(hcnt J a).1, (hcnt J b).1], by rw [(hcnt J a).2, (hcnt J b).2]⟩
            | cons d e =>
              have hlen := hg.2; rw [hin] at hlen; simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, t⟩
          · simp [stepForm, hop, hin, SForm.posCount, SForm.negCount]
          · simp only [stepForm, hop, hin, ↓reduceIte, SForm.posCount_neg, SForm.negCount_neg,
              List.head?_cons, Option.map_some, Option.getD_some]
            exact ⟨(hcnt J a).2, (hcnt J a).1⟩
      have hstep_mk : (stepForm fs g).markTuple =
          (let a := (g.inputs.head?.map (fun j => ts.getD j Z)).getD Z
           let b := (g.inputs[1]?.map (fun j => ts.getD j Z)).getD Z
           let cross := (a.1.1 ∩ b.1.2) ∪ (a.1.2 ∩ b.1.1)
           let u := a.2.1 ∪ b.2.1
           let v := a.2.2 ∪ b.2.2
           if g.op = GateOp.not then ((a.1.2, a.1.1), (a.2.2, a.2.1))
           else ((a.1.1 ∪ b.1.1, a.1.2 ∪ b.1.2),
             if g.op = GateOp.and then (u ∪ cross, v) else (u, v ∪ cross))) := by
        rcases hg.1 with hop | hop | hop
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, SForm.markTuple, SForm.posVars, SForm.negVars,
              SForm.andConf, SForm.orConf, Z]
          · simp only [stepForm, hop, hin, eq_self, reduceCtorEq, ↓reduceIte, List.head?_cons,
              Option.map_some, Option.getD_some, List.getElem?_cons_succ, List.getElem?_nil,
              Option.map_none, Option.getD_none]
            rw [← hmk a]
            exact mark_singleton_and _ _ _ _
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.head?_cons,
                Option.map_some, Option.getD_some, List.getElem?_cons_succ, List.getElem?_cons_zero]
              rw [← hmk a, ← hmk b]
              simp only [SForm.markTuple, SForm.posVars, SForm.negVars, SForm.andConf, SForm.orConf]
              convert rfl
            | cons d e =>
              have hlen := hg.2; rw [hin] at hlen; simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, c⟩⟩
          · simp [stepForm, hop, hin, SForm.markTuple, SForm.posVars, SForm.negVars,
              SForm.andConf, SForm.orConf, Z]
          · simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.head?_cons,
              Option.map_some, Option.getD_some, List.getElem?_cons_succ, List.getElem?_nil,
              Option.map_none, Option.getD_none]
            rw [← hmk a]
            exact mark_singleton_or _ _ _ _
          · cases c with
            | nil =>
              simp only [stepForm, hop, hin, reduceCtorEq, ↓reduceIte, List.head?_cons,
                Option.map_some, Option.getD_some, List.getElem?_cons_succ, List.getElem?_cons_zero]
              rw [← hmk a, ← hmk b]
              simp only [SForm.markTuple, SForm.posVars, SForm.negVars, SForm.andConf, SForm.orConf]
              convert rfl
            | cons d e =>
              have hlen := hg.2; rw [hin] at hlen; simp at hlen
        · rcases hin : g.inputs with _ | ⟨a, t⟩
          · simp [stepForm, hop, hin, SForm.markTuple, SForm.posVars, SForm.negVars,
              SForm.andConf, SForm.orConf, Z]
          · simp only [stepForm, hop, hin, ↓reduceIte, List.head?_cons,
              Option.map_some, Option.getD_some]
            rw [← hmk a]
            simp [SForm.markTuple, SForm.posVars_neg, SForm.negVars_neg,
              SForm.andConf_neg, SForm.orConf_neg]
      apply ih (stepF fs g) (fun J => stepC (zs J) g) (fun Y => stepW (ws Y) g) (stepM ts g) hrest
      · intro J; simp [stepF, stepC, hlenZ J]
      · intro Y; simp [stepF, stepW, hlenW Y]
      · simp [stepF, stepM, hlenT]
      · intro Y i
        simp only [stepF, stepW, getD_append_singleton, hlenW Y]
        by_cases h1 : i < (ws Y).length
        · rw [if_pos h1, if_pos h1]; exact hev Y i
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : i = (ws Y).length
          · rw [if_pos h2, if_pos h2]; exact hstep_ev Y
          · rw [if_neg h2, if_neg h2]; rfl
      · intro J i
        simp only [stepF, stepC, getD_append_singleton, hlenZ J]
        by_cases h1 : i < (zs J).length
        · rw [if_pos h1, if_pos h1]; exact hcnt J i
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : i = (zs J).length
          · rw [if_pos h2, if_pos h2]
            by_cases hnot : g.op = GateOp.not
            · rw [if_pos hnot]
              have hc := hstep_cnt J
              rw [if_pos hnot, if_pos hnot] at hc
              exact hc
            · rw [if_neg hnot]
              have hc := hstep_cnt J
              rw [if_neg hnot, if_neg hnot] at hc
              exact hc
          · rw [if_neg h2, if_neg h2]; exact ⟨rfl, rfl⟩
      · intro i
        simp only [stepF, stepM, getD_append_singleton, hlenT]
        by_cases h1 : i < ts.length
        · rw [if_pos h1, if_pos h1]; exact hmk i
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : i = ts.length
          · rw [if_pos h2, if_pos h2]; exact hstep_mk
          · rw [if_neg h2, if_neg h2]; rfl
  let fs0 : List (SForm k) := List.ofFn (fun j : Fin k => SForm.lit j true) ++ [.const false, .const true]
  let zs0 : Finset (Fin k) → List (Nat × Nat) := fun J =>
    List.ofFn (fun j : Fin k => ((if j ∈ J then 1 else 0, 0) : Nat × Nat)) ++ [(0, 0), (0, 0)]
  let ws0 : Finset (Fin k) → List Bool := fun Y =>
    List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false, true]
  let ts0 : List ((V × V) × (V × V)) :=
    List.ofFn (fun j : Fin k => ((({j}, ∅), (∅, ∅)) : (V × V) × (V × V))) ++ [Z, Z]
  have hgs : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hfit g hg
    exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
  have hbase := hgen D.gates fs0 zs0 ws0 ts0 hgs
    (fun J => by simp [fs0, zs0])
    (fun Y => by simp [fs0, ws0])
    (by simp [fs0, ts0])
    (fun Y i => by
      simp only [fs0, ws0, List.getD, List.getElem?_append, List.length_ofFn]
      by_cases h1 : i < k
      · rw [if_pos h1, if_pos h1]; simp [h1, SForm.eval]
      · rw [if_neg h1, if_neg h1]
        rcases i - k with _ | _ | m
        · rfl
        · rfl
        · have hf1 : ([SForm.const false, SForm.const true] : List (SForm k))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          have hf2 : ([false, true] : List Bool)[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          rw [hf1, hf2]; rfl)
    (fun J i => by
      simp only [fs0, zs0, List.getD, List.getElem?_append, List.length_ofFn]
      by_cases h1 : i < k
      · rw [if_pos h1, if_pos h1]; simp [h1, SForm.posCount, SForm.negCount]
      · rw [if_neg h1, if_neg h1]
        rcases i - k with _ | _ | m
        · exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
        · have hf1 : ([SForm.const false, SForm.const true] : List (SForm k))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          have hf2 : ([(0, 0), (0, 0)] : List (Nat × Nat))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          rw [hf1, hf2]; exact ⟨rfl, rfl⟩)
    (fun i => by
      simp only [fs0, ts0, List.getD, List.getElem?_append, List.length_ofFn]
      by_cases h1 : i < k
      · rw [if_pos h1, if_pos h1]
        simp [h1, SForm.markTuple, SForm.posVars, SForm.negVars, SForm.andConf, SForm.orConf]
      · rw [if_neg h1, if_neg h1]
        rcases i - k with _ | _ | m
        · rfl
        · rfl
        · have hf1 : ([SForm.const false, SForm.const true] : List (SForm k))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          have hf2 : ([Z, Z] : List ((V × V) × (V × V)))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          rw [hf1, hf2]; rfl)
  refine ⟨?_, ?_, ?_⟩
  · intro Y; exact hbase.1 Y D.output
  · intro J; exact (hbase.2.1 J D.output).1
  · exact hbase.2.2 D.output

lemma SForm.eval_mono_vars {k : Nat} (F : SForm k) {Y1 Y2 : Finset (Fin k)}
    (hpos : ∀ j ∈ F.posVars, j ∈ Y1 → j ∈ Y2)
    (hneg : ∀ j ∈ F.negVars, j ∈ Y2 → j ∈ Y1) :
    F.eval Y1 = true → F.eval Y2 = true := by
  induction F with
  | const b => exact id
  | lit j pol =>
    cases pol with
    | true =>
      simp only [SForm.eval, ↓reduceIte, decide_eq_true_eq]
      exact hpos j (by simp [SForm.posVars])
    | false =>
      simp only [SForm.eval, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true',
        decide_eq_false_iff_not]
      intro h1 h2
      exact h1 (hneg j (by simp [SForm.negVars]) h2)
  | and l r ihl ihr =>
    simp only [SForm.eval, Bool.and_eq_true]
    intro ⟨hl, hr⟩
    refine ⟨ihl (fun j hj => hpos j (by simp [SForm.posVars, hj]))
                (fun j hj => hneg j (by simp [SForm.negVars, hj])) hl,
            ihr (fun j hj => hpos j (by simp [SForm.posVars, hj]))
                (fun j hj => hneg j (by simp [SForm.negVars, hj])) hr⟩
  | or l r ihl ihr =>
    simp only [SForm.eval, Bool.or_eq_true]
    intro h
    rcases h with hl | hr
    · exact Or.inl (ihl (fun j hj => hpos j (by simp [SForm.posVars, hj]))
                        (fun j hj => hneg j (by simp [SForm.negVars, hj])) hl)
    · exact Or.inr (ihr (fun j hj => hpos j (by simp [SForm.posVars, hj]))
                        (fun j hj => hneg j (by simp [SForm.negVars, hj])) hr)

def SForm.repNeg {k : Nat} (J : Finset (Fin k)) (c : Bool) : SForm k → SForm k
  | .const b => .const b
  | .lit j pol => if pol = false ∧ j ∈ J then .const c else .lit j pol
  | .and l r => .and (l.repNeg J c) (r.repNeg J c)
  | .or l r => .or (l.repNeg J c) (r.repNeg J c)

lemma SForm.posCount_repNeg {k : Nat} (J : Finset (Fin k)) (c : Bool) (F : SForm k) :
    (F.repNeg J c).posCount J = F.posCount J := by
  induction F with
  | const _ => rfl
  | lit j pol =>
    cases pol with
    | true => simp [SForm.repNeg, SForm.posCount]
    | false =>
      simp only [SForm.repNeg, true_and, SForm.posCount, Bool.false_eq_true, false_and, ↓reduceIte]
      split_ifs <;> simp [SForm.posCount]
  | and l r ihl ihr => simp [SForm.repNeg, SForm.posCount, ihl, ihr]
  | or l r ihl ihr => simp [SForm.repNeg, SForm.posCount, ihl, ihr]

lemma SForm.negVars_repNeg_disjoint {k : Nat} (J : Finset (Fin k)) (c : Bool) (F : SForm k) :
    Disjoint (F.repNeg J c).negVars J := by
  induction F with
  | const _ => simp [SForm.repNeg, SForm.negVars]
  | lit j pol =>
    cases pol with
    | true => simp [SForm.repNeg, SForm.negVars]
    | false =>
      by_cases hj : j ∈ J
      · simp [SForm.repNeg, SForm.negVars, hj]
      · simp [SForm.repNeg, SForm.negVars, hj]
  | and l r ihl ihr =>
    simp only [SForm.repNeg, SForm.negVars]
    exact Finset.disjoint_union_left.mpr ⟨ihl, ihr⟩
  | or l r ihl ihr =>
    simp only [SForm.repNeg, SForm.negVars]
    exact Finset.disjoint_union_left.mpr ⟨ihl, ihr⟩

lemma SForm.eval_imp_repTrue {k : Nat} (J : Finset (Fin k)) (F : SForm k) (Y : Finset (Fin k)) :
    F.eval Y = true → (F.repNeg J true).eval Y = true := by
  induction F with
  | const _ => exact id
  | lit j pol =>
    cases pol with
    | true => simp [SForm.repNeg]
    | false =>
      by_cases hj : j ∈ J
      · simp [SForm.repNeg, hj, SForm.eval]
      · simp [SForm.repNeg, hj]
  | and l r ihl ihr =>
    simp only [SForm.repNeg, SForm.eval, Bool.and_eq_true]
    exact fun ⟨h1, h2⟩ => ⟨ihl h1, ihr h2⟩
  | or l r ihl ihr =>
    simp only [SForm.repNeg, SForm.eval, Bool.or_eq_true]
    exact fun h => h.elim (fun h1 => Or.inl (ihl h1)) (fun h2 => Or.inr (ihr h2))

lemma SForm.eval_false_imp_repFalse {k : Nat} (J : Finset (Fin k)) (F : SForm k) (Y : Finset (Fin k)) :
    F.eval Y = false → (F.repNeg J false).eval Y = false := by
  induction F with
  | const _ => exact id
  | lit j pol =>
    cases pol with
    | true => simp [SForm.repNeg]
    | false =>
      by_cases hj : j ∈ J
      · simp [SForm.repNeg, hj, SForm.eval]
      · simp [SForm.repNeg, hj]
  | and l r ihl ihr =>
    simp only [SForm.repNeg, SForm.eval, Bool.and_eq_false_iff]
    exact fun h => h.elim (fun h1 => Or.inl (ihl h1)) (fun h2 => Or.inr (ihr h2))
  | or l r ihl ihr =>
    simp only [SForm.repNeg, SForm.eval, Bool.or_eq_false_iff]
    exact fun ⟨h1, h2⟩ => ⟨ihl h1, ihr h2⟩

lemma SForm.repTrue_exists_sub {k : Nat} (J U : Finset (Fin k)) (hUJ : Disjoint U J) (F : SForm k)
    (hconf : Disjoint J F.andConf) :
    ∀ S ⊆ J, (F.repNeg J true).eval (U ∪ S) = true → ∃ S' ⊆ S, F.eval (U ∪ S') = true := by
  induction F with
  | const b =>
    intro S _ h; exact ⟨S, Finset.Subset.rfl, h⟩
  | lit j pol =>
    intro S _ h
    cases pol with
    | true => exact ⟨S, Finset.Subset.rfl, by simpa [SForm.repNeg] using h⟩
    | false =>
      by_cases hj : j ∈ J
      · refine ⟨∅, Finset.empty_subset _, ?_⟩
        have hjU : j ∉ U := Finset.disjoint_right.mp hUJ hj
        simp [SForm.eval, hjU]
      · exact ⟨S, Finset.Subset.rfl, by simpa [SForm.repNeg, hj] using h⟩
  | and l r ihl ihr =>
    intro S hSJ h
    simp only [SForm.repNeg, SForm.eval, Bool.and_eq_true] at h
    have hcl : Disjoint J l.andConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.andConf, hx]) hconf
    have hcr : Disjoint J r.andConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.andConf, hx]) hconf
    obtain ⟨S1, hS1S, h1⟩ := ihl hcl S hSJ h.1
    obtain ⟨S2, hS2S, h2⟩ := ihr hcr S hSJ h.2
    let S' := (S1 ∩ l.posVars) ∪ (S2 ∩ r.posVars)
    refine ⟨S', Finset.union_subset
      (Finset.Subset.trans Finset.inter_subset_left hS1S)
      (Finset.Subset.trans Finset.inter_subset_left hS2S), ?_⟩
    simp only [SForm.eval, Bool.and_eq_true]
    refine ⟨SForm.eval_mono_vars l ?_ ?_ h1, SForm.eval_mono_vars r ?_ ?_ h2⟩
    · intro j hj hmem
      simp only [Finset.mem_union] at hmem ⊢
      rcases hmem with hU | hS1
      · exact Or.inl hU
      · exact Or.inr (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hS1, hj⟩))
    · intro j hj hmem
      simp only [Finset.mem_union] at hmem ⊢
      rcases hmem with hU | hS'
      · exact Or.inl hU
      · rcases Finset.mem_union.mp hS' with hA | hB
        · exact Or.inr (Finset.mem_inter.mp hA).1
        · exfalso
          have hB' := Finset.mem_inter.mp hB
          have hjJ : j ∈ J := hSJ (hS2S hB'.1)
          have hjC : j ∈ (SForm.and l r).andConf := by
            simp [SForm.andConf, hj, hB'.2]
          exact Finset.disjoint_left.mp hconf hjJ hjC
    · intro j hj hmem
      simp only [Finset.mem_union] at hmem ⊢
      rcases hmem with hU | hS2
      · exact Or.inl hU
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hS2, hj⟩))
    · intro j hj hmem
      simp only [Finset.mem_union] at hmem ⊢
      rcases hmem with hU | hS'
      · exact Or.inl hU
      · rcases Finset.mem_union.mp hS' with hA | hB
        · exfalso
          have hA' := Finset.mem_inter.mp hA
          have hjJ : j ∈ J := hSJ (hS1S hA'.1)
          have hjC : j ∈ (SForm.and l r).andConf := by
            simp [SForm.andConf, hj, hA'.2]
          exact Finset.disjoint_left.mp hconf hjJ hjC
        · exact Or.inr (Finset.mem_inter.mp hB).1
  | or l r ihl ihr =>
    intro S hSJ h
    simp only [SForm.repNeg, SForm.eval, Bool.or_eq_true] at h
    have hcl : Disjoint J l.andConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.andConf, hx]) hconf
    have hcr : Disjoint J r.andConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.andConf, hx]) hconf
    rcases h with hl | hr
    · obtain ⟨S1, hS1S, h1⟩ := ihl hcl S hSJ hl
      exact ⟨S1, hS1S, by simp [SForm.eval, h1]⟩
    · obtain ⟨S2, hS2S, h2⟩ := ihr hcr S hSJ hr
      exact ⟨S2, hS2S, by simp [SForm.eval, h2]⟩

lemma SForm.repFalse_exists_sup {k : Nat} (J U : Finset (Fin k)) (F : SForm k)
    (hconf : Disjoint J F.orConf) :
    ∀ S ⊆ J, (F.repNeg J false).eval (U ∪ S) = false → ∃ S', S ⊆ S' ∧ S' ⊆ J ∧ F.eval (U ∪ S') = false := by
  induction F with
  | const b =>
    intro S hSJ h; exact ⟨S, Finset.Subset.rfl, hSJ, h⟩
  | lit j pol =>
    intro S hSJ h
    cases pol with
    | true => exact ⟨S, Finset.Subset.rfl, hSJ, by simpa [SForm.repNeg] using h⟩
    | false =>
      by_cases hj : j ∈ J
      · refine ⟨J, hSJ, Finset.Subset.rfl, ?_⟩
        simp [SForm.eval, hj]
      · exact ⟨S, Finset.Subset.rfl, hSJ, by simpa [SForm.repNeg, hj] using h⟩
  | and l r ihl ihr =>
    intro S hSJ h
    simp only [SForm.repNeg, SForm.eval, Bool.and_eq_false_iff] at h
    have hcl : Disjoint J l.orConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.orConf, hx]) hconf
    have hcr : Disjoint J r.orConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.orConf, hx]) hconf
    rcases h with hl | hr
    · obtain ⟨S1, hSS1, hS1J, h1⟩ := ihl hcl S hSJ hl
      exact ⟨S1, hSS1, hS1J, by simp [SForm.eval, h1]⟩
    · obtain ⟨S2, hSS2, hS2J, h2⟩ := ihr hcr S hSJ hr
      exact ⟨S2, hSS2, hS2J, by simp [SForm.eval, h2]⟩
  | or l r ihl ihr =>
    intro S hSJ h
    simp only [SForm.repNeg, SForm.eval, Bool.or_eq_false_iff] at h
    have hcl : Disjoint J l.orConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.orConf, hx]) hconf
    have hcr : Disjoint J r.orConf :=
      Finset.disjoint_of_subset_right (by intro x hx; simp [SForm.orConf, hx]) hconf
    obtain ⟨S1, hSS1, hS1J, h1⟩ := ihl hcl S hSJ h.1
    obtain ⟨S2, hSS2, hS2J, h2⟩ := ihr hcr S hSJ h.2
    let S' := S ∪ (S1 ∩ l.negVars) ∪ (S2 ∩ r.negVars)
    have hSS' : S ⊆ S' := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
    have hS'J : S' ⊆ J := Finset.union_subset
      (Finset.union_subset hSJ (Finset.Subset.trans Finset.inter_subset_left hS1J))
      (Finset.Subset.trans Finset.inter_subset_left hS2J)
    refine ⟨S', hSS', hS'J, ?_⟩
    simp only [SForm.eval, Bool.or_eq_false_iff]
    constructor
    · cases hlv : l.eval (U ∪ S') with
      | false => rfl
      | true =>
        exfalso
        have hlt : l.eval (U ∪ S1) = true := SForm.eval_mono_vars l ?_ ?_ hlv
        · rw [h1] at hlt; exact absurd hlt (by decide)
        · intro j hj hmem
          simp only [Finset.mem_union] at hmem ⊢
          rcases hmem with hU | hS'
          · exact Or.inl hU
          · rcases Finset.mem_union.mp hS' with hA | hB
            · rcases Finset.mem_union.mp hA with hS | h1n
              · exact Or.inr (hSS1 hS)
              · exact Or.inr (Finset.mem_inter.mp h1n).1
            · exfalso
              have hB' := Finset.mem_inter.mp hB
              have hjJ : j ∈ J := hS2J hB'.1
              have hjC : j ∈ (SForm.or l r).orConf := by
                simp [SForm.orConf, hj, hB'.2]
              exact Finset.disjoint_left.mp hconf hjJ hjC
        · intro j hj hmem
          simp only [Finset.mem_union] at hmem ⊢
          rcases hmem with hU | hS1
          · exact Or.inl hU
          · exact Or.inr (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hS1, hj⟩)))
    · cases hrv : r.eval (U ∪ S') with
      | false => rfl
      | true =>
        exfalso
        have hrt : r.eval (U ∪ S2) = true := SForm.eval_mono_vars r ?_ ?_ hrv
        · rw [h2] at hrt; exact absurd hrt (by decide)
        · intro j hj hmem
          simp only [Finset.mem_union] at hmem ⊢
          rcases hmem with hU | hS'
          · exact Or.inl hU
          · rcases Finset.mem_union.mp hS' with hA | hB
            · rcases Finset.mem_union.mp hA with hS | h1n
              · exact Or.inr (hSS2 hS)
              · exfalso
                have h1n' := Finset.mem_inter.mp h1n
                have hjJ : j ∈ J := hS1J h1n'.1
                have hjC : j ∈ (SForm.or l r).orConf := by
                  simp [SForm.orConf, hj, h1n'.2]
                exact Finset.disjoint_left.mp hconf hjJ hjC
            · exact Or.inr (Finset.mem_inter.mp hB).1
        · intro j hj hmem
          simp only [Finset.mem_union] at hmem ⊢
          rcases hmem with hU | hS2
          · exact Or.inl hU
          · exact Or.inr (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hS2, hj⟩))

lemma mono_eval_sub {k : Nat} (J U : Finset (Fin k)) (M : SForm k) (hmono : Disjoint M.negVars J)
    {S1 S2 : Finset (Fin k)} (hS12 : S1 ⊆ S2) (hS2J : S2 ⊆ J) :
    M.eval (U ∪ S1) = true → M.eval (U ∪ S2) = true := by
  apply SForm.eval_mono_vars M
  · intro j _ hmem
    exact Finset.union_subset_union_right hS12 hmem
  · intro j hj hmem
    simp only [Finset.mem_union] at hmem ⊢
    rcases hmem with hU | hS2
    · exact Or.inl hU
    · exact absurd (hS2J hS2) (Finset.disjoint_left.mp hmono hj)


end Formula1468


namespace Formula1468
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Build1470

def SForm.depth {k : Nat} : SForm k → Nat
  | .const _ => 0
  | .lit _ _ => 0
  | .and l r => max l.depth r.depth + 1
  | .or l r => max l.depth r.depth + 1

lemma SForm.depth_neg {k : Nat} (F : SForm k) : F.neg.depth = F.depth := by
  induction F with
  | const b => rfl
  | lit j p => rfl
  | and l r hl hr => simp [SForm.neg, SForm.depth, hl, hr]
  | or l r hl hr => simp [SForm.neg, SForm.depth, hl, hr]

lemma stepForm_depth {k : Nat} (fs : List (SForm k)) (ts : List Nat) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hv : ∀ j, (fs.getD j (.const false)).depth ≤ ts.getD j 0) :
    (stepForm fs g).depth ≤ Ftime 1 1 ts g := by
  classical
  rcases hg.1 with hop | hop | hop
  all_goals
    rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [stepForm, hop, hin, SForm.depth, Ftime]
    · have ha := hv a
      simp [stepForm, hop, hin, SForm.depth, SForm.depth_neg, Ftime] at * <;> omega
    · cases rest with
      | nil =>
        have ha := hv a
        have hb := hv b
        simp [stepForm, hop, hin, SForm.depth, SForm.depth_neg, Ftime] at * <;> omega
      | cons c cs =>
        have hh := hg.2
        simp [hin] at hh

lemma foldForm_depth {k : Nat} (gs : List Gate) (fs : List (SForm k))
    (ts : List Nat)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hlen : fs.length = ts.length)
    (hv : ∀ j, (fs.getD j (.const false)).depth ≤ ts.getD j 0) :
    ∀ j, ((gs.foldl (fun fs g => fs ++ [stepForm fs g]) fs).getD j (.const false)).depth ≤
      (sfold (Ftime 1 1) ts gs).getD j 0 := by
  induction gs generalizing fs ts with
  | nil => exact hv
  | cons g rest ih =>
    have hstep := stepForm_depth fs ts g (hg g (by simp)) hv
    have hrest : ∀ g ∈ rest, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2 := fun g h => hg g (by simp [h])
    change ∀ j, ((rest.foldl (fun fs g => fs ++ [stepForm fs g])
      (fs ++ [stepForm fs g])).getD j (.const false)).depth ≤
        (sfold (Ftime 1 1) (ts ++ [Ftime 1 1 ts g]) rest).getD j 0
    apply ih _ _ hrest (by simp [hlen])
    intro j
    rw [getD_append_singleton, getD_append_singleton, hlen]
    by_cases hj : j < ts.length
    · simp only [if_pos hj]
      exact hv j
    · simp only [if_neg hj]
      by_cases he : j = ts.length
      · simpa only [if_pos he] using hstep
      · simp only [if_neg he, SForm.depth, Nat.le_refl]

lemma canonical_depth {k : Nat} (D : Circuit) (hfit : FanInTwo D) :
    (canonical (k := k) D).depth ≤ delayX k 1 1 D := by
  let fs : List (SForm k) :=
    List.ofFn (fun j : Fin k => SForm.lit j true) ++ [.const false, .const true]
  have hz : fs.map SForm.depth = List.replicate (k + 2) 0 := by
    simp [fs, List.map_ofFn, Function.comp_def, SForm.depth, List.ofFn_const, List.replicate_add]
  apply foldForm_depth D.gates fs (List.replicate (k + 2) 0) hfit
  · simp [fs]
  · intro j
    have he := congrArg (fun xs : List Nat => xs.getD j 0) hz
    rw [show (0 : Nat) = SForm.depth (SForm.const (k := k) false) from rfl,
      List.getD_map] at he
    exact Nat.le_of_eq he

end Formula1468

namespace Lib1473Closure
open Formula1468
variable {k : Nat}

noncomputable def branch (F : SForm k) (K U : Finset (Fin k)) (up : Bool) (Y : Finset (Fin k)) : Bool :=
  (F.repNeg Kᶜ up).eval (U ∪ (Y∩Kᶜ))

theorem split_set (K X : Finset (Fin k)) : (X∩K)∪(X∩Kᶜ)=X := by
  classical
  ext j
  by_cases hj : j∈K <;> simp [hj]

theorem compl_disjoint {K U : Finset (Fin k)} (hu : U⊆K) : Disjoint U Kᶜ := by
  apply Finset.disjoint_left.mpr
  intro j hj hk
  exact (Finset.mem_compl.mp hk) (hu hj)

theorem up_iff (F : SForm k) (K Y : Finset (Fin k)) (hc : F.andConf⊆K) :
    (∃U⊆K,U⊆Y ∧ branch F K U true Y=true) ↔ ∃X⊆Y,F.eval X=true := by
  classical
  have hconf : Disjoint Kᶜ F.andConf := (compl_disjoint hc).symm
  constructor
  · rintro ⟨U,hUK,hUY,hv⟩
    obtain ⟨S,hSY,hF⟩ := F.repTrue_exists_sub Kᶜ U (compl_disjoint hUK) hconf
      (Y∩Kᶜ) Finset.inter_subset_right hv
    refine ⟨U∪S,Finset.union_subset hUY (hSY.trans Finset.inter_subset_left),hF⟩
  · rintro ⟨X,hXY,hF⟩
    refine ⟨X∩K,Finset.inter_subset_right,(Finset.inter_subset_left.trans hXY),?_⟩
    have hm := F.eval_imp_repTrue Kᶜ X hF
    have hsplit := split_set K X
    rw [←hsplit] at hm
    apply mono_eval_sub Kᶜ (X∩K) (F.repNeg Kᶜ true) (F.negVars_repNeg_disjoint Kᶜ true)
      (show X∩Kᶜ⊆Y∩Kᶜ from fun j hj=>Finset.mem_inter.mpr ⟨hXY (Finset.mem_inter.mp hj).1,(Finset.mem_inter.mp hj).2⟩)
      Finset.inter_subset_right hm

theorem down_iff (F : SForm k) (K Y : Finset (Fin k)) (hc : F.orConf⊆K) :
    (∀U⊆K,(∃j∈K \ U,j∈Y) ∨ branch F K U false Y=true) ↔ ∀X,Y⊆X→F.eval X=true := by
  classical
  have hconf : Disjoint Kᶜ F.orConf := (compl_disjoint hc).symm
  constructor
  · intro hall X hYX
    have hv := hall (X∩K) Finset.inter_subset_right
    have hn : ¬∃j∈K \ (X∩K),j∈Y := by
      rintro ⟨j,hj,hY⟩
      have h := Finset.mem_sdiff.mp hj
      exact h.2 (Finset.mem_inter.mpr ⟨hYX hY,h.1⟩)
    have hval := hv.resolve_left hn
    have hmono := mono_eval_sub Kᶜ (X∩K) (F.repNeg Kᶜ false) (F.negVars_repNeg_disjoint Kᶜ false)
      (show Y∩Kᶜ⊆X∩Kᶜ from fun j hj=>Finset.mem_inter.mpr ⟨hYX (Finset.mem_inter.mp hj).1,(Finset.mem_inter.mp hj).2⟩)
      (show X∩Kᶜ⊆Kᶜ from Finset.inter_subset_right) hval
    rw [split_set] at hmono
    by_contra hf
    have hf' : F.eval X=false := Bool.eq_false_iff.mpr hf
    have hmfalse := F.eval_false_imp_repFalse Kᶜ X hf'
    simp only [hmfalse,Bool.false_eq_true] at hmono
  · intro hall U hUK
    by_cases hguard : ∃j∈K \ U,j∈Y
    · exact Or.inl hguard
    · right
      by_contra hf
      have hf' : (F.repNeg Kᶜ false).eval (U∪(Y∩Kᶜ))=false := Bool.eq_false_iff.mpr hf
      obtain ⟨S,hYS,hSK,hfalse⟩ := F.repFalse_exists_sup Kᶜ U hconf (Y∩Kᶜ) Finset.inter_subset_right hf'
      have hsub : Y⊆U∪S := by
        intro j hj
        by_cases hjK : j∈K
        · apply Finset.mem_union_left
          by_contra hju
          exact hguard ⟨j,Finset.mem_sdiff.mpr ⟨hjK,hju⟩,hj⟩
        · exact Finset.mem_union_right _ (hYS (Finset.mem_inter.mpr ⟨hj,Finset.mem_compl.mpr hjK⟩))
      have htrue := hall (U∪S) hsub
      simp only [hfalse,Bool.false_eq_true] at htrue

end Lib1473Closure

namespace Build1470
open PEqualNP.CircuitLowerBounds

theorem bt_size (op : GateOp) (n h : Nat) :
    ∀ (C : Circuit) (L : List Nat), L ≠ [] → L.length ≤ 2^h →
      (bt op n h C L).1.size = C.size + (L.length-1) := by
  induction h with
  | zero =>
    intro C L hne hl
    have hp : 0 < L.length := List.length_pos_iff.mpr hne
    simp only [pow_zero] at hl
    simp only [bt]
    omega
  | succ h ih =>
    intro C L hne hl
    by_cases hl2 : L.length ≤ 2^h
    · simp only [bt,if_pos hl2]
      exact ih C L hne hl2
    · obtain ⟨h1,h2⟩ := split_ne h hl2
      obtain ⟨l1,l2⟩ := split_len h hl
      simp only [bt,if_neg hl2,appendGate_size]
      rw [ih _ _ h2 l2,ih _ _ h1 l1]
      simp only [List.length_take,List.length_drop]
      omega

end Build1470

namespace Build1470
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

def seqOp (op : GateOp) (n hf : ℕ) : Circuit → List (List ℕ) → Circuit × List ℕ
  | C, [] => (C, [])
  | C, G :: Gs => ((seqOp op n hf (bt op n hf C G).1 Gs).1,
      (bt op n hf C G).2 :: (seqOp op n hf (bt op n hf C G).1 Gs).2)

theorem seqOp_spec (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (n hf : ℕ) : ∀ (Gs : List (List ℕ)) (C : Circuit),
    (∀ G ∈ Gs, G ≠ [] ∧ G.length ≤ 2^hf ∧ ∀ j ∈ G, j < n + C.size) →
      C.gates <+: (seqOp op n hf C Gs).1.gates ∧ (seqOp op n hf C Gs).1.output = C.output ∧
      (seqOp op n hf C Gs).2.length = Gs.length ∧
      (∀ o ∈ (seqOp op n hf C Gs).2, o < n + (seqOp op n hf C Gs).1.size) ∧
      (FanInTwo C → FanInTwo (seqOp op n hf C Gs).1) ∧ (ReadsBack n C → ReadsBack n (seqOp op n hf C Gs).1) ∧
      notCount (seqOp op n hf C Gs).1 = notCount C ∧
      (∀ (β : Type) (F : List β → Gate → β) (init : List β) (d : β) (f : β → β → β),
        init.length = n → BinForm op F d f →
        (∀ o ∈ (seqOp op n hf C Gs).2, ∃ G ∈ Gs, semC F init d (seqOp op n hf C Gs).1 o = tfold f (semC F init d C) hf G) ∧
        (∀ G ∈ Gs, ∃ o ∈ (seqOp op n hf C Gs).2, semC F init d (seqOp op n hf C Gs).1 o = tfold f (semC F init d C) hf G)) := by
  intro Gs
  induction Gs with
  | nil =>
    intro C _
    refine ⟨List.prefix_refl _, rfl, rfl, by simp [seqOp], id, id, rfl, ?_⟩
    intro β F init d f _ _
    simp [seqOp]
  | cons G Gs ih =>
    intro C hG
    obtain ⟨g1, g2, g3⟩ := hG G (List.mem_cons_self ..)
    obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := bt_spec op hop n hf C G g1 g2 g3
    set C1 := (bt op n hf C G).1 with hC1
    set w1 := (bt op n hf C G).2 with hw1
    have hs1 : C.size ≤ C1.size := b1.length_le
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := ih C1 (fun G' hG' => by
      obtain ⟨x1, x2, x3⟩ := hG G' (List.mem_cons_of_mem _ hG')
      exact ⟨x1, x2, fun j hj => by have := x3 j hj; omega⟩)
    have e : seqOp op n hf C (G :: Gs) = ((seqOp op n hf C1 Gs).1, w1 :: (seqOp op n hf C1 Gs).2) := rfl
    rw [e]
    have hs2 : C1.size ≤ (seqOp op n hf C1 Gs).1.size := c1.length_le
    refine ⟨b1.trans c1, by rw [c2, b2], by simp [c3], ?_, fun hf' => c5 (b4 hf'), fun hr => c6 (b5 hr),
      by rw [c7, b6], ?_⟩
    · intro o ho
      simp only [List.mem_cons] at ho
      rcases ho with rfl | ho
      · show w1 < n + (seqOp op n hf C1 Gs).1.size
        omega
      · exact c4 o ho
    · intro β F init d f hi hb
      obtain ⟨d1, d2⟩ := c8 β F init d f hi hb
      have conv : ∀ G' ∈ Gs, tfold f (semC F init d C1) hf G' = tfold f (semC F init d C) hf G' := by
        intro G' hG'
        obtain ⟨x1, _, x3⟩ := hG G' (List.mem_cons_of_mem _ hG')
        exact tfold_congr f hf G' _ _ x1 (fun j hj => semC_prefix F init d b1 (by rw [hi]; exact x3 j hj))
      have first : semC F init d (seqOp op n hf C1 Gs).1 w1 = tfold f (semC F init d C) hf G := by
        rw [semC_prefix F init d c1 (by rw [hi]; exact b3), b7 β F init d f hi hb]
      constructor
      · intro o ho
        simp only [List.mem_cons] at ho
        rcases ho with rfl | ho
        · exact ⟨G, List.mem_cons_self .., first⟩
        · obtain ⟨G', hG', e'⟩ := d1 o ho
          exact ⟨G', List.mem_cons_of_mem _ hG', by rw [e', conv G' hG']⟩
      · intro G' hG'
        simp only [List.mem_cons] at hG'
        rcases hG' with rfl | hG'
        · exact ⟨w1, List.mem_cons_self .., first⟩
        · obtain ⟨o, ho, e'⟩ := d2 G' hG'
          exact ⟨o, List.mem_cons_of_mem _ ho, by rw [e', conv G' hG']⟩


end Build1470

namespace Build1470
open PEqualNP.CircuitLowerBounds

theorem seqOp_size (op : GateOp) (n hf : Nat) :
    ∀ (Gs : List (List Nat)) (C : Circuit),
      (∀ G ∈ Gs, G ≠ [] ∧ G.length ≤ 2^hf) →
      (seqOp op n hf C Gs).1.size = C.size + (Gs.map (fun G => G.length-1)).sum := by
  intro Gs
  induction Gs with
  | nil => intro C _; simp [seqOp]
  | cons G Gs ih =>
    intro C hGs
    have hg := hGs G (List.mem_cons_self ..)
    have hs := ih (bt op n hf C G).1 (fun H hH => hGs H (List.mem_cons_of_mem _ hH))
    change (seqOp op n hf (bt op n hf C G).1 Gs).1.size = _
    rw [hs,bt_size op n hf C G hg.1 hg.2]
    simp only [List.map_cons,List.sum_cons]
    omega

end Build1470

namespace Build1470
open PEqualNP.CircuitLowerBounds

theorem bt_singleton (op : GateOp) (n h : Nat) (C : Circuit) (a : Nat) :
    bt op n h C [a] = (C,a) := by
  induction h with
  | zero => simp [bt]
  | succ h ih =>
    have hp : 0 < (2:Nat)^h := pow_pos (by decide) _
    have hh : [a].length ≤ (2:Nat)^h := by simp only [List.length_singleton]; omega
    simp only [bt,if_pos hh,ih]

theorem seqOp_singleton (op : GateOp) (n h : Nat) (C : Circuit) (a : Nat) :
    seqOp op n h C [[a]] = (C,[a]) := by
  simp only [seqOp,bt_singleton]

end Build1470


namespace Lib1473Guards
variable {k : Nat}

noncomputable def assignments (K : Finset (Fin k)) : List (Finset (Fin k)) := K.powerset.toList

@[simp] theorem mem_assignments (K U : Finset (Fin k)) : U∈assignments K ↔ U⊆K := by
  classical
  simp [assignments]

@[simp] theorem assignments_length (K : Finset (Fin k)) : (assignments K).length=2^K.card := by
  classical
  simp [assignments]

theorem assignments_ne_nil (K : Finset (Fin k)) : assignments K≠[] := by
  have hh := assignments_length K
  have hp := Nat.two_pow_pos K.card
  intro he
  rw [he] at hh
  simp only [List.length_nil] at hh
  omega

@[simp] theorem assignments_empty : assignments (∅ : Finset (Fin k))=[∅] := by
  classical
  simp [assignments]

noncomputable def pins (K U : Finset (Fin k)) (up : Bool) : Finset (Fin k) := if up then U else K \ U

noncomputable def row (K U : Finset (Fin k)) (up : Bool) (p : Finset (Fin k)→Nat) : List Nat :=
  p U::(pins K U up).toList.map Fin.val

noncomputable def rows (K : Finset (Fin k)) (up : Bool) (p : Finset (Fin k)→Nat) : List (List Nat) :=
  (assignments K).map (fun U=>row K U up p)

@[simp] theorem row_ne_nil (K U : Finset (Fin k)) (up : Bool) (p : Finset (Fin k)→Nat) :
    row K U up p≠[] := by simp [row]

theorem row_length (K U : Finset (Fin k)) (hU : U⊆K) (up : Bool) (p : Finset (Fin k)→Nat) :
    (row K U up p).length≤K.card+1 := by
  classical
  simp only [row,List.length_cons,List.length_map,Finset.length_toList]
  have hh : pins K U up⊆K := by cases up <;> simp only [pins,Bool.false_eq_true,if_false,if_true];exact Finset.sdiff_subset;exact hU
  exact Nat.add_le_add_right (Finset.card_le_card hh) 1

@[simp] theorem rows_length (K : Finset (Fin k)) (up : Bool) (p : Finset (Fin k)→Nat) :
    (rows K up p).length=2^K.card := by simp [rows]

theorem rows_ne_nil (K : Finset (Fin k)) (up : Bool) (p : Finset (Fin k)→Nat) :
    rows K up p≠[] := by
  have hh := rows_length K up p
  have hp := Nat.two_pow_pos K.card
  intro he
  rw [he] at hh
  simp only [List.length_nil] at hh
  omega

@[simp] theorem rows_empty (up : Bool) (p : Finset (Fin k)→Nat) : rows ∅ up p=[[p ∅]] := by
  classical
  cases up <;> simp [rows,row,pins]

theorem row_live (K U : Finset (Fin k)) (hU : U⊆K) (up : Bool) (p : Finset (Fin k)→Nat)
    (N : Nat) (hk : k≤N) (hp : p U < N) : ∀a∈row K U up p,a < N := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hp
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    exact j.isLt.trans_le hk

theorem row_depth (K U : Finset (Fin k)) (up : Bool) (p : Finset (Fin k)→Nat)
    (v : Nat→Nat) (depth : Nat) (hp : v (p U)≤depth) (hv : ∀j : Fin k,v j.val=0) :
    ∀a∈row K U up p,v a≤depth := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hp
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    rw [hv]
    exact Nat.zero_le _

theorem row_and (K U Y : Finset (Fin k)) (p : Finset (Fin k)→Nat) (v : Nat→Bool)
    (hv : ∀j : Fin k,v j.val=true ↔ j∈Y) :
    (∀a∈row K U true p,v a=true) ↔ v (p U)=true ∧ U⊆Y := by
  classical
  simp only [row,pins,if_true,List.forall_mem_cons,List.forall_mem_map,Finset.mem_toList]
  exact and_congr_right (fun _=>forall_congr' (fun j=>imp_congr_right (fun _=>hv j)))

theorem row_or (K U Y : Finset (Fin k)) (p : Finset (Fin k)→Nat) (v : Nat→Bool)
    (hv : ∀j : Fin k,v j.val=true ↔ j∈Y) :
    (∃a∈row K U false p,v a=true) ↔ v (p U)=true ∨ ∃j∈K \ U,j∈Y := by
  classical
  simp only [row,pins,Bool.false_eq_true,if_false,List.mem_cons,List.mem_map]
  constructor
  · rintro ⟨a,(rfl | ⟨j,hj,rfl⟩),ha⟩
    · exact Or.inl ha
    · exact Or.inr ⟨j,Finset.mem_toList.mp hj,(hv j).mp ha⟩
  · rintro (ha | ⟨j,hj,hY⟩)
    · exact ⟨p U,Or.inl rfl,ha⟩
    · exact ⟨j.val,Or.inr ⟨j,Finset.mem_toList.mpr hj,rfl⟩,(hv j).mpr hY⟩

end Lib1473Guards

namespace Lib1473Aggregate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Build1470 Lib1473Guards

def op (b : Bool) : GateOp := if b then .and else .or

def comb (b x y : Bool) : Bool := if b then x && y else x || y

def Select {α : Type*} (b : Bool) (L : List α) (P : α→Prop) : Prop :=
  if b then ∀a∈L,P a else ∃a∈L,P a

theorem allowed (b : Bool) : op b=.and ∨ op b=.or := by cases b <;> simp [op]

theorem bin_val (b : Bool) : BinForm (op b) Fval false (comb b) := by
  cases b <;> intro W a c <;> simp [op,comb,Fval,GateOp.eval]

theorem bin_time (b : Bool) : BinForm (op b) (Ftime 1 1) 0 (fun x y=>max x y+1) := by
  cases b <;> intro W a c <;> simp [op,Ftime]

theorem fold_truth (b : Bool) (h : Nat) (L : List Nat) (v : Nat→Bool)
    (hn : L≠[]) (hl : L.length≤2^h) :
    tfold (comb b) v h L=true ↔ Select b L (fun a=>v a=true) := by
  cases b with
  | false =>
    change tfold (fun x y => x || y) v h L = true ↔ ∃ a ∈ L, v a = true
    rw [tfold_any h L v hn hl,List.any_eq_true]
  | true =>
    change tfold (fun x y => x && y) v h L = true ↔ ∀ a ∈ L, v a = true
    rw [tfold_all h L v hn hl,List.all_eq_true]

theorem select_transfer {α β : Type*} (b : Bool) (L : List α) (M : List β) (P : α→Prop) (Q : β→Prop)
    (hl : ∀a∈L,∃c∈M,P a↔Q c) (hm : ∀c∈M,∃a∈L,P a↔Q c) :
    Select b L P ↔ Select b M Q := by
  cases b with
  | false =>
    constructor
    · rintro ⟨a,ha,hp⟩
      obtain ⟨c,hc,hq⟩ := hl a ha
      exact ⟨c,hc,hq.mp hp⟩
    · rintro ⟨c,hc,hq⟩
      obtain ⟨a,ha,hp⟩ := hm c hc
      exact ⟨a,ha,hp.mpr hq⟩
  | true =>
    constructor
    · intro h c hc
      obtain ⟨a,ha,hq⟩ := hm c hc
      exact hq.mp (h a ha)
    · intro h a ha
      obtain ⟨c,hc,hq⟩ := hl a ha
      exact hq.mpr (h c hc)

noncomputable def aggregate {k : Nat} (K : Finset (Fin k)) (up : Bool)
    (C : Circuit) (p : Finset (Fin k)→Nat) : Circuit :=
  let A := seqOp (op up) (k+2) (Nat.clog 2 (K.card+1)) C (rows K up p)
  let B := bt (op (!up)) (k+2) K.card A.1 A.2
  withOutput B.1 B.2

theorem aggregate_empty {k : Nat} (up : Bool) (C : Circuit) (p : Finset (Fin k)→Nat) :
    aggregate (∅ : Finset (Fin k)) up C p=withOutput C (p ∅) := by
  simp only [aggregate,rows_empty,seqOp_singleton,bt_singleton]

theorem aggregate_spec {k : Nat} (K : Finset (Fin k)) (up : Bool)
    (C : Circuit) (p : Finset (Fin k)→Nat) (depth : Nat)
    (hf : FanInTwo C) (hr : ReadsBack (k+2) C)
    (hp : ∀U⊆K,p U < k+2+C.size)
    (hd : ∀U⊆K,semC (Ftime 1 1) (List.replicate (k+2) 0) 0 C (p U)≤depth) :
    let E := aggregate K up C p
    FanInTwo E ∧ ReadsBack (k+2) E ∧ E.output < k+2+E.size ∧ notCount E=notCount C ∧
    E.size≤C.size+(K.card+1)*2^K.card ∧
    delayX k 1 1 E≤depth+Nat.clog 2 (K.card+1)+K.card ∧
    ∀Y : Finset (Fin k),valX E E.output Y=true ↔
      Select (!up) (rows K up p) (fun G=>Select up G (fun a=>semC Fval (inpX Y) false C a=true)) := by
  classical
  let h := Nat.clog 2 (K.card+1)
  have hG : ∀G∈rows K up p,G≠[] ∧ G.length≤2^h ∧ ∀a∈G,a < k+2+C.size := by
    intro G hG
    obtain ⟨U,hU,rfl⟩ := List.mem_map.mp hG
    have hu := (mem_assignments K U).mp hU
    refine ⟨row_ne_nil K U up p,(row_length K U hu up p).trans (Nat.le_pow_clog (by decide) _),?_⟩
    exact row_live K U hu up p (k+2+C.size) (by omega) (hp U hu)
  obtain ⟨s1,s2,s3,s4,s5,s6,s7,s8⟩ := seqOp_spec (op up) (allowed up) (k+2) h (rows K up p) C hG
  let A := seqOp (op up) (k+2) h C (rows K up p)
  have hlen : A.2.length=2^K.card := by rw [s3,rows_length]
  have hne : A.2≠[] := by
    intro hh
    have ht:=Nat.two_pow_pos K.card
    rw [hh,List.length_nil] at hlen
    omega
  obtain ⟨t1,t2,t3,t4,t5,t6,t7⟩ := bt_spec (op (!up)) (allowed (!up)) (k+2) K.card A.1 A.2 hne (le_of_eq hlen) s4
  let B := bt (op (!up)) (k+2) K.card A.1 A.2
  refine ⟨t4 (s5 hf),t5 (s6 hr),t3,t6.trans s7,?_,?_,?_⟩
  · have hz := seqOp_size (op up) (k+2) h (rows K up p) C (fun G hg=>⟨(hG G hg).1,(hG G hg).2.1⟩)
    have hz' := bt_size (op (!up)) (k+2) K.card A.1 A.2 hne (le_of_eq hlen)
    have hb : ((rows K up p).map (fun G=>G.length-1)).sum≤2^K.card*K.card := by
      have hh := List.sum_le_length_nsmul ((rows K up p).map (fun G=>G.length-1)) K.card (by
        intro a ha
        obtain ⟨G,hG,rfl⟩ := List.mem_map.mp ha
        obtain ⟨U,hU,rfl⟩ := List.mem_map.mp hG
        have hl := row_length K U ((mem_assignments K U).mp hU) up p
        omega)
      simpa only [List.length_map,rows_length,Nat.nsmul_eq_mul] using hh
    change B.1.size≤C.size+(K.card+1)*2^K.card
    change A.1.size=_ at hz
    rw [hz',hz,hlen]
    have hsub := Nat.sub_le (2^K.card) 1
    nlinarith
  · change semC (Ftime 1 1) (List.replicate (k+2) 0) 0 B.1 B.2≤_
    rw [t7 Nat (Ftime 1 1) (List.replicate (k+2) 0) 0 (fun x y=>max x y+1) (by simp) (bin_time (!up))]
    obtain ⟨ds,_⟩ := s8 Nat (Ftime 1 1) (List.replicate (k+2) 0) 0 (fun x y=>max x y+1) (by simp) (bin_time up)
    have hb : ∀a∈A.2,semC (Ftime 1 1) (List.replicate (k+2) 0) 0 A.1 a≤depth+h := by
      intro a ha
      obtain ⟨G,hGG,he⟩ := ds a ha
      rw [he]
      obtain ⟨U,hU,rfl⟩ := List.mem_map.mp hGG
      have hu := (mem_assignments K U).mp hU
      have hraw (j : Fin k) : semC (Ftime 1 1) (List.replicate (k+2) 0) 0 C j.val=0 := by
        unfold semC
        rw [sfold_old _ _ _ _ (by simp;omega)]
        simp
      have hh := tfold_le 1 h (row K U up p) _ depth (row_ne_nil K U up p)
        (row_depth K U up p _ depth (hd U hu) hraw)
      simpa only [Nat.mul_one] using hh
    simpa only [Nat.mul_one] using tfold_le 1 K.card A.2 _ (depth+h) hne hb
  · intro Y
    change semC Fval (inpX Y) false B.1 B.2=true ↔ _
    rw [t7 Bool Fval (inpX Y) false (comb (!up)) (inpX_length Y) (bin_val (!up)),
      fold_truth (!up) K.card A.2 _ hne (le_of_eq hlen)]
    obtain ⟨ds,dt⟩ := s8 Bool Fval (inpX Y) false (comb up) (inpX_length Y) (bin_val up)
    apply select_transfer
    · intro a ha
      obtain ⟨G,hGG,he⟩ := ds a ha
      refine ⟨G,hGG,?_⟩
      rw [he]
      exact fold_truth up h G _ (hG G hGG).1 (hG G hGG).2.1
    · intro G hGG
      obtain ⟨a,ha,he⟩ := dt G hGG
      refine ⟨a,ha,?_⟩
      rw [he]
      exact fold_truth up h G _ (hG G hGG).1 (hG G hGG).2.1

end Lib1473Aggregate

namespace Lib1473Closure
open Formula1468 Lib1473Guards Lib1473Aggregate
variable {k : Nat}

theorem selection_meaning (F : SForm k) (K Y : Finset (Fin k)) (up : Bool)
    (p : Finset (Fin k)→Nat) (v : Nat→Bool)
    (hv : ∀j : Fin k,v j.val=true ↔ j∈Y)
    (hp : ∀U⊆K,v (p U)=branch F K U up Y)
    (hc : (if up then F.andConf else F.orConf)⊆K) :
    Select (!up) (rows K up p) (fun G=>Select up G (fun a=>v a=true)) ↔
      if up then ∃X⊆Y,F.eval X=true else ∀X,Y⊆X→F.eval X=true := by
  classical
  cases up with
  | true =>
    change (∃G∈rows K true p,∀a∈G,v a=true) ↔ ∃X⊆Y,F.eval X=true
    rw [←up_iff F K Y hc]
    constructor
    · rintro ⟨G,hG,hval⟩
      obtain ⟨U,hU,rfl⟩ := List.mem_map.mp hG
      have hu := (mem_assignments K U).mp hU
      have h := (row_and K U Y p v hv).mp hval
      exact ⟨U,hu,h.2,by rw [←hp U hu];exact h.1⟩
    · rintro ⟨U,hU,hUY,hval⟩
      refine ⟨row K U true p,List.mem_map.mpr ⟨U,(mem_assignments K U).mpr hU,rfl⟩,?_⟩
      apply (row_and K U Y p v hv).mpr
      exact ⟨by rw [hp U hU];exact hval,hUY⟩
  | false =>
    change (∀G∈rows K false p,∃a∈G,v a=true) ↔ ∀X,Y⊆X→F.eval X=true
    rw [←down_iff F K Y hc]
    constructor
    · intro hall U hU
      have h := hall (row K U false p) (List.mem_map.mpr ⟨U,(mem_assignments K U).mpr hU,rfl⟩)
      rcases (row_or K U Y p v hv).mp h with h | h
      · exact Or.inr (by rw [←hp U hU];exact h)
      · exact Or.inl h
    · intro hall G hG
      obtain ⟨U,hU,rfl⟩ := List.mem_map.mp hG
      have hu := (mem_assignments K U).mp hU
      apply (row_or K U Y p v hv).mpr
      rcases hall U hu with h | h
      · exact Or.inr h
      · exact Or.inl (by rw [hp U hu];exact h)

end Lib1473Closure

namespace Lib1473Dual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Build1470
open Formula1468

noncomputable def Focc (zs : List (Nat × Nat)) (g : Gate) : Nat × Nat :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let ab := g.inputs.foldl (fun acc j =>
    let z := zs.getD j (0,0)
    (acc.1+z.1,acc.2+z.2)) (0,0)
  let h := (g.inputs.head?.map (fun j => zs.getD j (0,0))).getD (0,0)
  if g.op = GateOp.not then (h.2,h.1) else ab

def seeds (k : Nat) : List (Nat × Nat) :=
  List.replicate k (1,0) ++ [(0,0),(0,0)]

noncomputable def time (k : Nat) (C : Circuit) (w : Nat) : Nat :=
  semC (Ftime 1 1) (List.replicate (k+2) 0) 0 C w

noncomputable def weight (k : Nat) (C : Circuit) (w : Nat) : Nat :=
  (semC Focc (seeds k) (0,0) C w).1

def constWire (k : Nat) (b : Bool) : Nat := if b then k+1 else k

noncomputable def den {k : Nat} (K U : Finset (Fin k)) (up : Bool)
    (f : SForm k) (Y : Finset (Fin k)) : Bool :=
  (f.repNeg Kᶜ up).eval (U ∪ (Y ∩ Kᶜ))

structure Signal {k : Nat} (K U : Finset (Fin k)) (up : Bool)
    (C : Circuit) (f : SForm k) (w : Nat) : Prop where
  live : w < k+2+C.size
  truth : ∀ Y, semC Fval (inpX Y) false C w = den K U up f Y
  depth : time k C w ≤ f.depth
  count : weight k C w ≤ f.posCount Finset.univ

theorem semC_raw {α : Type} (F : List α → Gate → α) (init : List α) (d : α)
    (C : Circuit) (w : Nat) (hw : w < init.length) :
    semC F init d C w = init.getD w d := sfold_old F init C.gates d hw

theorem Signal.extend {k : Nat} {K U : Finset (Fin k)} {up : Bool}
    {C D : Circuit} {f : SForm k} {w : Nat} (h : Signal K U up C f w)
    (hp : C.gates <+: D.gates) : Signal K U up D f w := by
  have hs : C.size ≤ D.size := hp.length_le
  refine ⟨by have := h.live; omega,?_,?_,?_⟩
  · intro Y
    rw [semC_prefix Fval (inpX Y) false hp (by rw [inpX_length]; exact h.live)]
    exact h.truth Y
  · unfold time
    rw [semC_prefix (Ftime 1 1) _ 0 hp (by simpa using h.live)]
    exact h.depth
  · unfold weight
    rw [semC_prefix Focc (seeds k) (0,0) hp (by simpa [seeds] using h.live)]
    exact h.count

theorem constant {k : Nat} (K U : Finset (Fin k)) (up b : Bool) (C : Circuit) :
    Signal K U up C (.const b) (constWire k b) := by
  classical
  refine ⟨by cases b <;> simp [constWire] <;> omega,?_,?_,?_⟩
  · intro Y
    rw [semC_raw Fval (inpX Y) false C _ (by cases b <;> simp [constWire,inpX_length])]
    cases b <;> simp only [constWire,Bool.false_eq_true,ite_false,ite_true,inpX_k,inpX_k1,den,SForm.repNeg,SForm.eval]
  · unfold time
    rw [semC_raw _ _ _ C _ (by cases b <;> simp [constWire])]
    cases b <;> simp [constWire,SForm.depth,List.getD_eq_getElem?_getD]
  · unfold weight
    rw [semC_raw _ _ _ C _ (by cases b <;> simp [constWire,seeds])]
    cases b <;> simp [constWire,seeds,SForm.posCount,List.getD_eq_getElem?_getD]

theorem positive_input {k : Nat} (K U : Finset (Fin k)) (up : Bool) (C : Circuit)
    (hU : U ⊆ K) (j : Fin k) (hj : j ∉ K) :
    Signal K U up C (.lit j true) j.val := by
  classical
  have hu : j ∉ U := fun h => hj (hU h)
  refine ⟨by omega,?_,?_,?_⟩
  · intro Y
    rw [semC_raw Fval (inpX Y) false C _ (by rw [inpX_length]; omega), inpX_fin]
    simp [den,SForm.repNeg,SForm.eval,hj,hu]
  · unfold time
    rw [semC_raw _ _ _ C _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD,j.isLt,SForm.depth]
  · unfold weight
    rw [semC_raw _ _ _ C _ (by simp [seeds]; omega)]
    simp [seeds,List.getD_eq_getElem?_getD,List.getElem?_append_left,j.isLt,SForm.posCount]

theorem literal {k : Nat} (K U : Finset (Fin k)) (up : Bool) (C : Circuit)
    (hU : U ⊆ K) (j : Fin k) (pol : Bool) :
    ∃ w, Signal K U up C (.lit j pol) w := by
  classical
  by_cases hj : j ∈ K
  · let b := if pol then decide (j ∈ U) else !decide (j ∈ U)
    have h := constant K U up b C
    refine ⟨constWire k b,h.live,?_,?_,?_⟩
    · intro Y
      rw [h.truth]
      cases pol <;> simp [den,SForm.repNeg,SForm.eval,hj,b]
    · simpa [SForm.depth] using h.depth
    · have hh : weight k C (constWire k b) ≤ 0 := h.count
      exact hh.trans (Nat.zero_le _)
  · cases pol with
    | true => exact ⟨j.val,positive_input K U up C hU j hj⟩
    | false =>
      have h := constant K U up up C
      refine ⟨constWire k up,h.live,?_,?_,?_⟩
      · intro Y
        rw [h.truth]
        simp [den,SForm.repNeg,SForm.eval,hj]
      · simpa [SForm.depth] using h.depth
      · simpa [SForm.posCount] using h.count

theorem and_signal {k : Nat} {K U : Finset (Fin k)} {up : Bool} {C : Circuit}
    {f g : SForm k} {a b : Nat} (ha : Signal K U up C f a) (hb : Signal K U up C g b) :
    Signal K U up (appendAnd C a b) (.and f g) (k+2+C.size) := by
  refine ⟨by simp [appendAnd_size],?_,?_,?_⟩
  · intro Y
    have he := semC_append Fval (inpX Y) false C ⟨.and,[a,b]⟩
    rw [inpX_length] at he
    unfold appendAnd
    rw [he]
    simpa [Fval,GateOp.eval,den,SForm.repNeg,SForm.eval,semC,id_eq] using
      congrArg₂ (fun x y : Bool => x && y) (ha.truth Y) (hb.truth Y)
  · unfold time appendAnd
    rw [show k+2+C.size = (List.replicate (k+2) 0).length+C.size by simp,
      semC_append]
    simp only [Ftime, List.foldl_cons, List.foldl_nil, reduceCtorEq, if_false, if_true, Nat.zero_max]
    change max (time k C a) (time k C b)+1 ≤ max f.depth g.depth+1
    exact Nat.add_le_add_right (max_le_max ha.depth hb.depth) 1
  · unfold weight appendAnd
    rw [show k+2+C.size = (seeds k).length+C.size by simp [seeds], semC_append]
    simp only [Focc, List.foldl_cons, List.foldl_nil, reduceCtorEq, if_false, Nat.zero_add]
    change weight k C a + weight k C b ≤ f.posCount Finset.univ + g.posCount Finset.univ
    exact Nat.add_le_add ha.count hb.count

theorem or_signal {k : Nat} {K U : Finset (Fin k)} {up : Bool} {C : Circuit}
    {f g : SForm k} {a b : Nat} (ha : Signal K U up C f a) (hb : Signal K U up C g b) :
    Signal K U up (appendOr C a b) (.or f g) (k+2+C.size) := by
  refine ⟨by simp [appendOr_size],?_,?_,?_⟩
  · intro Y
    have he := semC_append Fval (inpX Y) false C ⟨.or,[a,b]⟩
    rw [inpX_length] at he
    unfold appendOr
    rw [he]
    simpa [Fval,GateOp.eval,den,SForm.repNeg,SForm.eval,semC,id_eq] using
      congrArg₂ (fun x y : Bool => x || y) (ha.truth Y) (hb.truth Y)
  · unfold time appendOr
    rw [show k+2+C.size = (List.replicate (k+2) 0).length+C.size by simp,
      semC_append]
    simp only [Ftime, List.foldl_cons, List.foldl_nil, reduceCtorEq, if_false, if_true, Nat.zero_max]
    change max (time k C a) (time k C b)+1 ≤ max f.depth g.depth+1
    exact Nat.add_le_add_right (max_le_max ha.depth hb.depth) 1
  · unfold weight appendOr
    rw [show k+2+C.size = (seeds k).length+C.size by simp [seeds], semC_append]
    simp only [Focc, List.foldl_cons, List.foldl_nil, reduceCtorEq, if_false, Nat.zero_add]
    change weight k C a + weight k C b ≤ f.posCount Finset.univ + g.posCount Finset.univ
    exact Nat.add_le_add ha.count hb.count

end Lib1473Dual

namespace Lib1473Dual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Build1470
open Formula1468

theorem neg_neg {k : Nat} (f : SForm k) : f.neg.neg = f := by
  induction f with
  | const b => simp [SForm.neg]
  | lit j p => simp [SForm.neg]
  | and f g hf hg => simp [SForm.neg,hf,hg]
  | or f g hf hg => simp [SForm.neg,hf,hg]

def HasPair {k : Nat} (K U : Finset (Fin k)) (up : Bool) (C : Circuit) (f : SForm k) : Prop :=
  ∃ p n, Signal K U up C f p ∧ Signal K U up C f.neg n

theorem HasPair.extend {k : Nat} {K U : Finset (Fin k)} {up : Bool}
    {C D : Circuit} {f : SForm k} (h : HasPair K U up C f) (hp : C.gates <+: D.gates) :
    HasPair K U up D f := by
  obtain ⟨p,n,hp',hn⟩ := h
  exact ⟨p,n,hp'.extend hp,hn.extend hp⟩

theorem HasPair.neg {k : Nat} {K U : Finset (Fin k)} {up : Bool}
    {C : Circuit} {f : SForm k} (h : HasPair K U up C f) : HasPair K U up C f.neg := by
  obtain ⟨p,n,hp,hn⟩ := h
  exact ⟨n,p,hn,by simpa only [neg_neg] using hp⟩

theorem constant_pair {k : Nat} (K U : Finset (Fin k)) (up b : Bool) (C : Circuit) :
    HasPair K U up C (.const b) :=
  ⟨constWire k b,constWire k (!b),constant K U up b C,constant K U up (!b) C⟩

theorem and_pair {k : Nat} {K U : Finset (Fin k)} {up : Bool} (C : Circuit)
    (hf : FanInTwo C) (hr : ReadsBack (k+2) C) (f g : SForm k)
    (hfp : HasPair K U up C f) (hgp : HasPair K U up C g) :
    ∃ D, FanInTwo D ∧ ReadsBack (k+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size = C.size+2 ∧ HasPair K U up D (.and f g) := by
  obtain ⟨fp,fn,hfp,hfn⟩ := hfp
  obtain ⟨gp,gn,hgp,hgn⟩ := hgp
  let B := appendAnd C fp gp
  have hp : C.gates <+: B.gates := appendGate_prefix C _
  have bf : FanInTwo B := appendAnd_fanInTwo hf
  have br : ReadsBack (k+2) B := appendAnd_readsBack hr hfp.live hgp.live
  have hfn' := hfn.extend hp
  have hgn' := hgn.extend hp
  let D := appendOr B fn gn
  have hp' : B.gates <+: D.gates := appendGate_prefix B _
  refine ⟨D,appendOr_fanInTwo bf,appendOr_readsBack br hfn'.live hgn'.live,
    hp.trans hp',?_,?_,?_⟩
  · simp only [D,B,appendOr_notCount,appendAnd_notCount]
  · simp only [D,B,appendOr_size,appendAnd_size]
  · exact ⟨k+2+C.size,k+2+B.size,(and_signal hfp hgp).extend hp',
      or_signal hfn' hgn'⟩

theorem or_pair {k : Nat} {K U : Finset (Fin k)} {up : Bool} (C : Circuit)
    (hf : FanInTwo C) (hr : ReadsBack (k+2) C) (f g : SForm k)
    (hfp : HasPair K U up C f) (hgp : HasPair K U up C g) :
    ∃ D, FanInTwo D ∧ ReadsBack (k+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size = C.size+2 ∧ HasPair K U up D (.or f g) := by
  obtain ⟨fp,fn,hfp,hfn⟩ := hfp
  obtain ⟨gp,gn,hgp,hgn⟩ := hgp
  let B := appendOr C fp gp
  have hp : C.gates <+: B.gates := appendGate_prefix C _
  have bf : FanInTwo B := appendOr_fanInTwo hf
  have br : ReadsBack (k+2) B := appendOr_readsBack hr hfp.live hgp.live
  have hfn' := hfn.extend hp
  have hgn' := hgn.extend hp
  let D := appendAnd B fn gn
  have hp' : B.gates <+: D.gates := appendGate_prefix B _
  refine ⟨D,appendAnd_fanInTwo bf,appendAnd_readsBack br hfn'.live hgn'.live,
    hp.trans hp',?_,?_,?_⟩
  · simp only [D,B,appendAnd_notCount,appendOr_notCount]
  · simp only [D,B,appendAnd_size,appendOr_size]
  · exact ⟨k+2+C.size,k+2+B.size,(or_signal hfp hgp).extend hp',
      and_signal hfn' hgn'⟩

theorem step_build {k : Nat} (K U : Finset (Fin k)) (up : Bool)
    (C : Circuit) (hf : FanInTwo C) (hr : ReadsBack (k+2) C)
    (fs : List (SForm k)) (hfs : ∀ j, HasPair K U up C (fs.getD j (.const false)))
    (g : Gate) (hg : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    ∃ D, FanInTwo D ∧ ReadsBack (k+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size ≤ C.size+2 ∧ HasPair K U up D (stepForm fs g) := by
  have same {f : SForm k} (h : HasPair K U up C f) :
      ∃ D, FanInTwo D ∧ ReadsBack (k+2) D ∧ C.gates <+: D.gates ∧
        notCount D = notCount C ∧ D.size ≤ C.size+2 ∧ HasPair K U up D f :=
    ⟨C,hf,hr,List.prefix_rfl,rfl,by omega,h⟩
  rcases hg with hg | hg | hg
  · rcases hi : g.inputs with _ | ⟨a, _ | ⟨b,tail⟩⟩
    · simpa only [stepForm,hg,hi] using same (constant_pair K U up true C)
    · simpa only [stepForm,hg,hi] using same (hfs a)
    · obtain ⟨D,df,dr,hp,hn,hs,hh⟩ := and_pair C hf hr _ _ (hfs a) (hfs b)
      exact ⟨D,df,dr,hp,hn,hs.le,by simpa only [stepForm,hg,hi] using hh⟩
  · rcases hi : g.inputs with _ | ⟨a, _ | ⟨b,tail⟩⟩
    · simpa only [stepForm,hg,hi] using same (constant_pair K U up false C)
    · simpa only [stepForm,hg,hi] using same (hfs a)
    · obtain ⟨D,df,dr,hp,hn,hs,hh⟩ := or_pair C hf hr _ _ (hfs a) (hfs b)
      exact ⟨D,df,dr,hp,hn,hs.le,by simpa only [stepForm,hg,hi] using hh⟩
  · rcases hi : g.inputs with _ | ⟨a,tail⟩
    · simpa only [stepForm,hg,hi] using same (constant_pair K U up true C)
    · simpa only [stepForm,hg,hi] using same (hfs a).neg

theorem fold_build {k : Nat} (K U : Finset (Fin k)) (up : Bool) (gs : List Gate)
    (hg : ∀ g ∈ gs,g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (C : Circuit) (hf : FanInTwo C) (hr : ReadsBack (k+2) C)
    (fs : List (SForm k)) (hfs : ∀ j,HasPair K U up C (fs.getD j (.const false))) :
    ∃ D, FanInTwo D ∧ ReadsBack (k+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size ≤ C.size+2*gs.length ∧
      ∀ j,HasPair K U up D
        ((gs.foldl (fun fs g => fs++[stepForm fs g]) fs).getD j (.const false)) := by
  induction gs generalizing C fs with
  | nil => exact ⟨C,hf,hr,List.prefix_rfl,rfl,by simp,hfs⟩
  | cons g gs ih =>
    obtain ⟨B,bf,br,hp,hn,hs,hh⟩ := step_build K U up C hf hr fs hfs g
      (hg g (List.mem_cons_self ..))
    have hfs' (j : Nat) : HasPair K U up B ((fs++[stepForm fs g]).getD j (.const false)) := by
      rw [getD_append_singleton]
      split_ifs
      · exact (hfs j).extend hp
      · exact hh
      · exact constant_pair K U up false B
    obtain ⟨D,df,dr,hp',hn',hs',hh'⟩ := ih
      (fun g h => hg g (List.mem_cons_of_mem _ h)) B bf br _ hfs'
    refine ⟨D,df,dr,hp.trans hp',hn'.trans hn,?_,hh'⟩
    simp only [List.length_cons]
    omega

theorem branch {k : Nat} (K U : Finset (Fin k)) (up : Bool) (hU : U ⊆ K)
    (D C : Circuit) (hD : FanInTwo D) (hf : FanInTwo C) (hr : ReadsBack (k+2) C) :
    ∃ B p, FanInTwo B ∧ ReadsBack (k+2) B ∧ C.gates <+: B.gates ∧
      notCount B = notCount C ∧ B.size ≤ C.size+2*D.size ∧
      Signal K U up B (canonical D) p := by
  classical
  let fs := List.ofFn (fun j : Fin k => SForm.lit j true)++[.const false,.const true]
  have hs (j : Nat) : HasPair K U up C (fs.getD j (.const false)) := by
    by_cases hj : j < k
    · have he : fs.getD j (.const false) = .lit ⟨j,hj⟩ true := by
        simp [fs,List.getD_eq_getElem?_getD,List.getElem?_append_left,hj]
      rw [he]
      obtain ⟨p,hp⟩ := literal K U up C hU ⟨j,hj⟩ true
      obtain ⟨n,hn⟩ := literal K U up C hU ⟨j,hj⟩ false
      exact ⟨p,n,hp,hn⟩
    · have he : fs.getD j (.const false) =
          ([.const false,.const true] : List (SForm k)).getD (j-k) (.const false) := by
        have hk : (List.ofFn (fun i : Fin k => SForm.lit i true)).length ≤ j := by
          simp only [List.length_ofFn]
          omega
        simpa only [fs,List.length_ofFn] using
          (List.getD_append_right (List.ofFn (fun i : Fin k => SForm.lit i true))
            ([.const false,.const true] : List (SForm k)) (.const false) j hk)
      rw [he]
      rcases hd : j-k with _ | _ | q
      · exact constant_pair K U up false C
      · exact constant_pair K U up true C
      · have he' : ([.const false,.const true] : List (SForm k)).getD (q+2) (.const false) =
            .const false := by simp [List.getD_eq_getElem?_getD]
        rw [he']; exact constant_pair K U up false C
  obtain ⟨B,bf,br,hp,hn,hsize,hw⟩ := fold_build K U up D.gates
    (fun g hg => (hD g hg).1) C hf hr fs hs
  obtain ⟨p,n,hpos,hneg⟩ := hw D.output
  exact ⟨B,p,bf,br,hp,hn,hsize,hpos⟩

end Lib1473Dual

namespace Lib1473Dual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Build1470
open Formula1468

theorem branch_list {k : Nat} (K : Finset (Fin k)) (up : Bool)
    (D : Circuit) (hD : FanInTwo D) (Us : List (Finset (Fin k)))
    (hUs : ∀ U ∈ Us,U ⊆ K) (C : Circuit) (hf : FanInTwo C) (hr : ReadsBack (k+2) C) :
    ∃ (B : Circuit) (p : Finset (Fin k) → Nat), FanInTwo B ∧ ReadsBack (k+2) B ∧ C.gates <+: B.gates ∧
      notCount B = notCount C ∧ B.size ≤ C.size+Us.length*(2*D.size) ∧
      ∀ U ∈ Us,Signal K U up B (canonical D) (p U) := by
  classical
  induction Us generalizing C with
  | nil => exact ⟨C,fun _=>0,hf,hr,List.prefix_rfl,rfl,by simp,by simp⟩
  | cons U Us ih =>
    obtain ⟨A,a,af,ar,hp,hn,hs,ha⟩ := branch K U up (hUs U (List.mem_cons_self ..)) D C hD hf hr
    obtain ⟨B,p,bf,br,hp',hn',hs',hh⟩ := ih
      (fun V hv=>hUs V (List.mem_cons_of_mem _ hv)) A af ar
    refine ⟨B,fun V=>if V=U then a else p V,bf,br,hp.trans hp',hn'.trans hn,?_,?_⟩
    · simp only [List.length_cons]
      calc
        B.size ≤ A.size+Us.length*(2*D.size) := hs'
        _ ≤ (C.size+2*D.size)+Us.length*(2*D.size) := Nat.add_le_add_right hs _
        _ = C.size+(Us.length+1)*(2*D.size) := by ring
    · intro V hv
      by_cases he : V=U
      · subst V
        simpa only [ite_true] using ha.extend hp'
      · simp only [he,ite_false]
        exact hh V ((List.mem_cons.mp hv).resolve_left he)

theorem family {k : Nat} (K : Finset (Fin k)) (up : Bool)
    (D : Circuit) (hD : FanInTwo D) :
    ∃ (C : Circuit) (p : Finset (Fin k) → Nat), FanInTwo C ∧ ReadsBack (k+2) C ∧
      notCount C = 0 ∧ C.size ≤ 2^K.card*(2*D.size) ∧
      ∀ U ⊆ K,Signal K U up C (canonical D) (p U) := by
  classical
  obtain ⟨C,p,hf,hr,hprefix,hn,hs,hv⟩ := branch_list K up D hD K.powerset.toList
    (by intro U hu; exact Finset.mem_powerset.mp (Finset.mem_toList.mp hu))
    emptyCircuit emptyCircuit_fanInTwo (emptyCircuit_readsBack (k+2))
  refine ⟨C,p,hf,hr,hn,?_,?_⟩
  · simpa only [Finset.length_toList,Finset.card_powerset,emptyCircuit_size,Nat.zero_add] using hs
  · intro U hu
    exact hv U (Finset.mem_toList.mpr (Finset.mem_powerset.mpr hu))

end Lib1473Dual


namespace Lib1473Final

theorem size_bound (s d c e : Nat)
    (hc : c ≤ 2^d * (2*s)) (he : e ≤ c + (d+1)*2^d) :
    e ≤ 4 * 2^d * (s+d+1) := by
  calc
    e ≤ 2^d * (2*s) + (d+1)*2^d := he.trans (Nat.add_le_add_right hc _)
    _ ≤ 4 * 2^d * (s+d+1) := by nlinarith [Nat.zero_le (2^d*s), Nat.zero_le (2^d*d)]

theorem depth_bound (s d c e : Nat)
    (hc : c ≤ s) (he : e ≤ c + Nat.clog 2 (d+1) + d) :
    e ≤ s + d + Nat.clog 2 (d+1) + 2 := by omega

end Lib1473Final

namespace Lib1473Final
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Build1470
open Formula1468 Lib1473Dual Lib1473Aggregate

lemma canonical_weight {k : Nat} (D : Circuit) (hD : FanInTwo D) :
    (canonical (k := k) D).posCount Finset.univ = weight k D D.output := by
  classical
  have h := (canonical_spec (k := k) D hD).2.1 (Finset.univ : Finset (Fin k))
  simpa [weight, semC, sfold, Focc, seeds, List.ofFn_const] using h

lemma weight_withOutput (k : Nat) (C : Circuit) (w : Nat) :
    weight k (withOutput C w) (withOutput C w).output = weight k C w := by rfl

lemma aggregate_empty_count {k : Nat} (up : Bool) (D C : Circuit)
    (p : Finset (Fin k) → Nat) (hD : FanInTwo D)
    (hs : Signal (k := k) ∅ ∅ up C (canonical (k := k) D) (p ∅)) :
    let E := aggregate (∅ : Finset (Fin k)) up C p
    weight k E E.output ≤ weight k D D.output := by
  dsimp only
  rw [aggregate_empty, weight_withOutput]
  exact hs.count.trans_eq (canonical_weight D hD)

end Lib1473Final

namespace Lib1473Final
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Build1470
open Formula1468
open Lib1473Dual Lib1473Aggregate

 theorem closure_circuit {k : Nat} (D : Circuit) (K : Finset (Fin k)) (up : Bool)
    (hD : FanInTwo D)
    (hc : (if up then (canonical D).andConf else (canonical D).orConf) ⊆ K) :
    ∃ E : Circuit, (FanInTwo E ∧ ReadsBack (k+2) E ∧ E.output < k+2+E.size) ∧
      notCount E = 0 ∧ E.size ≤ 4*2^K.card*(D.size+K.card+1) ∧
      delayX k 1 1 E ≤ delayX k 1 1 D + K.card + Nat.clog 2 (K.card+1) + 2 ∧
      (K = ∅ → weight k E E.output ≤ weight k D D.output) ∧
      ∀ Y : Finset (Fin k), valX E E.output Y = true ↔
        if up then ∃ X ⊆ Y, valX D D.output X = true
        else ∀ X, Y ⊆ X → valX D D.output X = true := by
  classical
  obtain ⟨C,p,hf,hr,hn,hs,hp⟩ := family K up D hD
  obtain ⟨ef,er,eo,en,esz,ed,ev⟩ := aggregate_spec K up C p (canonical D).depth hf hr
    (fun U hU => (hp U hU).live) (fun U hU => (hp U hU).depth)
  refine ⟨aggregate K up C p,⟨ef,er,eo⟩,en.trans hn,
    size_bound D.size K.card C.size _ hs esz,
    depth_bound (delayX k 1 1 D) K.card (canonical D).depth _ (canonical_depth D hD) ed,?_,?_⟩
  · intro hK
    subst K
    exact aggregate_empty_count up D C p hD (hp ∅ (Finset.Subset.refl _))
  · intro Y
    have hv (j : Fin k) : semC Fval (inpX Y) false C j.val = true ↔ j ∈ Y := by
      rw [semC_raw Fval (inpX Y) false C j.val (by rw [inpX_length]; omega),inpX_fin]
      simp only [decide_eq_true_eq]
    have hb (U : Finset (Fin k)) (hU : U ⊆ K) :
        semC Fval (inpX Y) false C (p U) = Lib1473Closure.branch (canonical D) K U up Y :=
      (hp U hU).truth Y
    have he := (ev Y).trans (Lib1473Closure.selection_meaning (canonical D) K Y up p
      (fun a => semC Fval (inpX Y) false C a) hv hb hc)
    have hval (X : Finset (Fin k)) : (canonical D).eval X = valX D D.output X := by
      have hinit : (List.ofFn (fun j : Fin k => @decide (j ∈ X) (Classical.propDecidable _)) ++ [false,true]) = inpX X := by
        unfold inpX
        apply congrArg (fun f : Fin k → Bool => List.ofFn f ++ [false,true])
        funext j
        exact congrArg (@decide (j ∈ X)) (Subsingleton.elim _ _)
      have hx := (canonical_spec D hD).1 X
      rw [hinit] at hx
      exact hx
    simpa only [hval] using he

end Lib1473Final

end PEqualNP.Outside.L_lib_1473_aux

open PEqualNP.Outside.L_lib_1473_aux in
theorem PEqualNP.Outside.L_lib_1473 :
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let valid := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) D ∧ D.output < k+2+D.size
  let run := fun {k : Nat} (D : PEqualNP.CircuitLowerBounds.Circuit) (Y : Finset (Fin k)) =>
    ((D.wires (List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true])).getD D.output false)
  let delay := fun (k c e : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    let times := D.gates.foldl (fun (ts : List Nat) g =>
      let mx := g.inputs.foldl (fun v j => max v (ts.getD j 0)) 0
      ts ++ [if g.op=PEqualNP.CircuitLowerBounds.GateOp.not then ((g.inputs.head?.map (fun j => ts.getD j 0)).getD 0)
        else mx+(if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then c else e)]) (List.replicate (k+2) 0)
    times.getD D.output 0
  let occ := fun {k : Nat} (J : Finset (Fin k)) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    let xs := List.ofFn (fun j : Fin k => ((if j ∈ J then 1 else 0, 0) : Nat × Nat)) ++ [(0,0),(0,0)]
    let ws := D.gates.foldl (fun (zs : List (Nat × Nat)) g =>
      let ab := g.inputs.foldl (fun (acc : Nat × Nat) j =>
        let z := zs.getD j (0,0)
        (acc.1+z.1,acc.2+z.2)) (0,0)
      let h := (g.inputs.head?.map (fun j => zs.getD j (0,0))).getD (0,0)
      zs ++ [if g.op=PEqualNP.CircuitLowerBounds.GateOp.not then (h.2,h.1) else ab]) xs
    ws.getD D.output (0,0)
  let marks := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    let V := Finset (Fin k)
    let Z : (V × V) × (V × V) := ((∅,∅),(∅,∅))
    let xs := List.ofFn (fun j : Fin k => ((({j},∅),(∅,∅)) : (V × V) × (V × V))) ++ [Z,Z]
    let ws := D.gates.foldl (fun (ts : List ((V × V) × (V × V))) g =>
      let a := (g.inputs.head?.map (fun j => ts.getD j Z)).getD Z
      let b := (g.inputs[1]?.map (fun j => ts.getD j Z)).getD Z
      let cross := (a.1.1 ∩ b.1.2) ∪ (a.1.2 ∩ b.1.1)
      let u := a.2.1 ∪ b.2.1
      let v := a.2.2 ∪ b.2.2
      ts ++ [if g.op=PEqualNP.CircuitLowerBounds.GateOp.not then ((a.1.2,a.1.1),(a.2.2,a.2.1))
        else ((a.1.1 ∪ b.1.1,a.1.2 ∪ b.1.2),
          if g.op=PEqualNP.CircuitLowerBounds.GateOp.and then (u ∪ cross,v) else (u,v ∪ cross))]) xs
    ws.getD D.output Z
  ∀ (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) (K : Finset (Fin k)) (up : Bool),
    valid k D → (if up then (marks k D).2.1 else (marks k D).2.2) ⊆ K →
    ∃ E : PEqualNP.CircuitLowerBounds.Circuit, valid k E ∧ PEqualNP.NotBracket.notCount E=0 ∧
      E.size ≤ 4 * 2^K.card * (D.size+K.card+1) ∧
      delay k 1 1 E ≤ delay k 1 1 D + K.card + Nat.clog 2 (K.card+1) + 2 ∧
      (K=∅ → (occ (Finset.univ : Finset (Fin k)) E).1 ≤ (occ (Finset.univ : Finset (Fin k)) D).1) ∧
      ∀ Y : Finset (Fin k), run E Y=true ↔
        if up then ∃ X : Finset (Fin k), X ⊆ Y ∧ run D X=true
        else ∀ X : Finset (Fin k), Y ⊆ X → run D X=true
:= by
  classical
  dsimp only
  intro k D K up hD hc
  have hm := (Formula1468.canonical_spec (k := k) D hD.1).2.2
  have hconf : (if up then (Formula1468.canonical D).andConf
      else (Formula1468.canonical D).orConf) ⊆ K := by
    change (if up then (Formula1468.canonical D).markTuple.2.1
      else (Formula1468.canonical D).markTuple.2.2) ⊆ K
    rw [hm]
    by_cases hu : up = true
    · simpa only [if_pos hu] using hc
    · simpa only [if_neg hu] using hc
  have hall := Lib1473Final.closure_circuit D K up hD.1 hconf
  unfold Build1470.valX Build1470.inpX Build1470.delayX Lib1473Dual.weight
    Build1470.semC Build1470.sfold Build1470.Ftime Lib1473Dual.Focc Lib1473Dual.seeds at hall
  simp only [Finset.mem_univ,ite_true,List.ofFn_const] at hall ⊢
  convert hall using 1 <;> congr! 16
  all_goals try apply congrArg List.ofFn
  all_goals funext j
  all_goals exact congrArg (@decide _) (Subsingleton.elim _ _)
