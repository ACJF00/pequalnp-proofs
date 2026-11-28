import PEqualNP.Defs
import Mathlib.Data.Fintype.Sort

namespace PEqualNP.Outside.L_lib_1436_aux


namespace Base

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

abbrev Input (n : ℕ) := Fin n → Bool

variable {n m : ℕ} (P N : Input n → Fin m → Prop)

theorem reach_zero (x : Input n) : Reach P N 0 x := trivial

theorem reach_succ (k : ℕ) (x : Input n) : Reach P N (k+1) x ↔
    ∃ u v j, Reach P N k u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j := Iff.rfl

theorem reach_mono (k : ℕ) : Monotone (Reach P N k) := by
  intro x y xy active
  cases k with
  | zero => exact reach_zero P N y
  | succ k =>
    obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
    exact (reach_succ P N k y).mpr ⟨u,v,j,prior,uv,vx.trans xy,pu,nv⟩

theorem reach_pred {k : ℕ} {x : Input n} (active : Reach P N (k+1) x) : Reach P N k x := by
  obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
  exact reach_mono P N k (uv.trans vx) prior

theorem reach_of_le {k l : ℕ} {x : Input n} (bound : k ≤ l) (active : Reach P N l x) :
    Reach P N k x := by
  induction bound with
  | refl => exact active
  | step _ ih => exact ih (reach_pred P N active)

noncomputable def support : Finset (Input n) := by
  classical
  exact Finset.univ.filter (fun x => ∃ j, P x j ∨ N x j)

theorem mem_support (x : Input n) : x ∈ support P N ↔ ∃ j, P x j ∨ N x j := by
  classical
  simp [support]

theorem cone_iff (u x : Input n) : u ≤ x ↔ ∀ i, u i = true → x i = true := by
  constructor
  · intro below i active
    exact Bool.le_iff_imp.mp (below i) active
  · intro on i
    exact Bool.le_iff_imp.mpr (on i)

theorem reach_support {k : ℕ} (positive : 0 < k) (x : Input n) : Reach P N k x ↔
    ∃ v ∈ support P N, v ≤ x ∧ Reach P N k v := by
  constructor
  · intro active
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨u,v,j,prior,uv,vx,pu,nv⟩ := (reach_succ P N k x).mp active
      refine ⟨v,(mem_support P N v).mpr ⟨j,Or.inr nv⟩,vx,?_⟩
      exact (reach_succ P N k v).mpr ⟨u,v,j,prior,uv,le_rfl,pu,nv⟩
  · rintro ⟨v,_,vx,active⟩
    exact reach_mono P N k vx active

private noncomputable def levels (d : ℕ) (x : Input n) : Finset ℕ := by
  classical
  exact (Finset.range (d+1)).filter (fun k => Reach P N k x)

private theorem mem_levels (d : ℕ) (x : Input n) (k : ℕ) :
    k ∈ levels P N d x ↔ k ≤ d ∧ Reach P N k x := by
  classical
  simp [levels,Nat.lt_succ_iff]

private theorem levels_nonempty (d : ℕ) (x : Input n) : (levels P N d x).Nonempty :=
  ⟨0,(mem_levels P N d x 0).mpr ⟨Nat.zero_le _,reach_zero P N x⟩⟩

noncomputable def rank (d : ℕ) (x : Input n) : ℕ :=
  (levels P N d x).max' (levels_nonempty P N d x)

theorem rank_bound (d : ℕ) (x : Input n) : rank P N d x ≤ d :=
  ((mem_levels P N d x _).mp (Finset.max'_mem _ (levels_nonempty P N d x))).1

theorem rank_reaches (d : ℕ) (x : Input n) : Reach P N (rank P N d x) x :=
  ((mem_levels P N d x _).mp (Finset.max'_mem _ (levels_nonempty P N d x))).2

theorem level_le_rank {d k : ℕ} {x : Input n} (small : k ≤ d) (active : Reach P N k x) :
    k ≤ rank P N d x :=
  Finset.le_max' (levels P N d x) k ((mem_levels P N d x k).mpr ⟨small,active⟩)

theorem rank_mono (d : ℕ) : Monotone (rank P N d) := by
  intro x y xy
  exact level_le_rank P N (rank_bound P N d x) (reach_mono P N _ xy (rank_reaches P N d x))

theorem rank_threshold_iff {d k : ℕ} {x : Input n} (small : k ≤ d) :
    k ≤ rank P N d x ↔ Reach P N k x :=
  ⟨fun below => reach_of_le P N below (rank_reaches P N d x), level_le_rank P N small⟩

theorem rank_grows {d : ℕ} (bounded : ∀ x, ¬ Reach P N (d+1) x)
    {u v : Input n} {j : Fin m} (uv : u ≤ v) (pu : P u j) (nv : N v j) :
    rank P N d u < rank P N d v := by
  have next : Reach P N (rank P N d u + 1) v :=
    (reach_succ P N _ v).mpr ⟨u,v,j,rank_reaches P N d u,uv,le_rfl,pu,nv⟩
  have room : rank P N d u + 1 ≤ d := by
    by_contra notRoom
    exact bounded v (reach_of_le P N (by omega : d+1 ≤ rank P N d u+1) next)
  exact Nat.lt_of_succ_le (level_le_rank P N room next)

theorem threshold_support (d : ℕ) {k : ℕ} (positive : 0 < k) (x : Input n) :
    k ≤ rank P N d x ↔ ∃ v ∈ support P N, v ≤ x ∧ k ≤ rank P N d v := by
  constructor
  · intro high
    have small : k ≤ d := high.trans (rank_bound P N d x)
    obtain ⟨v,mem,vx,active⟩ := (reach_support P N positive x).mp
      ((rank_threshold_iff P N small).mp high)
    exact ⟨v,mem,vx,level_le_rank P N small active⟩
  · rintro ⟨v,_,vx,high⟩
    exact high.trans (rank_mono P N d vx)

noncomputable def rankBucket (d k : ℕ) : Finset (Input n) := by
  classical
  exact (support P N).filter (fun x => rank P N d x = k)

theorem mem_rankBucket (d k : ℕ) (x : Input n) :
    x ∈ rankBucket P N d k ↔ x ∈ support P N ∧ rank P N d x = k := by
  classical
  simp [rankBucket]

theorem rank_bucket_count (d : ℕ) :
    (∑ k ∈ Finset.range (d+1), (rankBucket P N d k).card) = (support P N).card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise (s := support P N) (t := Finset.range (d+1))
    (f := rank P N d) (by
      intro x _
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (rank_bound P N d x)))).symm

theorem threshold_buckets (d : ℕ) {k : ℕ} (positive : 0 < k) (x : Input n) :
    k ≤ rank P N d x ↔ ∃ l, k ≤ l ∧ l ≤ d ∧ ∃ v ∈ rankBucket P N d l, v ≤ x := by
  constructor
  · intro on
    obtain ⟨v,mem,vx,below⟩ := (threshold_support P N d positive x).mp on
    exact ⟨rank P N d v,below,rank_bound P N d v,v,(mem_rankBucket P N d _ _).mpr ⟨mem,rfl⟩,vx⟩
  · rintro ⟨l,kl,_,v,mem,vx⟩
    obtain ⟨supportV,level⟩ := (mem_rankBucket P N d l v).mp mem
    exact (threshold_support P N d positive x).mpr ⟨v,supportV,vx,level.symm ▸ kl⟩

noncomputable def positiveInputs (j : Fin m) : Finset (Input n) := by
  classical
  exact Finset.univ.filter (fun x => P x j)

noncomputable def positivePairs : Finset (Input n × Fin m) := by
  classical
  exact Finset.univ.filter (fun z => P z.1 z.2)

theorem mem_positiveInputs (j : Fin m) (x : Input n) : x ∈ positiveInputs P j ↔ P x j := by
  classical
  simp [positiveInputs]

theorem mem_positivePairs (z : Input n × Fin m) : z ∈ positivePairs P ↔ P z.1 z.2 := by
  classical
  simp [positivePairs]

theorem positive_input_support {j : Fin m} {x : Input n} (positive : x ∈ positiveInputs P j) :
    x ∈ support P N :=
  (mem_support P N x).mpr ⟨j,Or.inl ((mem_positiveInputs P j x).mp positive)⟩

theorem positive_incidence_count :
    (∑ j : Fin m, (positiveInputs P j).card) = (positivePairs P).card := by
  classical
  calc
    _ = ∑ j : Fin m, ((positivePairs P).filter (fun z => z.2 = j)).card := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.card_nbij' (fun x : Input n => (x,j)) Prod.fst
      · intro x present
        exact Finset.mem_filter.mpr ⟨(mem_positivePairs P _).mpr ((mem_positiveInputs P _ _).mp present),rfl⟩
      · intro z present
        obtain ⟨member,eq⟩ := Finset.mem_filter.mp present
        exact (mem_positiveInputs P _ _).mpr (eq ▸ (mem_positivePairs P z).mp member)
      · intro x _
        rfl
      · intro z present
        exact Prod.ext rfl (Finset.mem_filter.mp present).2.symm
    _ = _ := (Finset.card_eq_sum_card_fiberwise (s := positivePairs P) (t := Finset.univ)
      (f := Prod.snd) (by
        intro j _
        exact Finset.mem_univ _)).symm

def guardedCone (d : ℕ) (u x : Input n) : Prop :=
  u ≤ x ∧ ¬ rank P N d u + 1 ≤ rank P N d x

def tapAccepts (d : ℕ) (x : Input n) (j : Fin m) : Prop :=
  ∃ u ∈ positiveInputs P j, guardedCone P N d u x

theorem tap_accepts_positive (d : ℕ) {x : Input n} {j : Fin m} (positive : P x j) :
    tapAccepts P N d x j := by
  refine ⟨x,(mem_positiveInputs P j x).mpr positive,le_rfl,?_⟩
  omega

theorem tap_rejects_negative {d : ℕ} (bounded : ∀ x, ¬ Reach P N (d+1) x)
    {x : Input n} {j : Fin m} (negative : N x j) : ¬ tapAccepts P N d x j := by
  rintro ⟨u,mem,ux,below⟩
  have grows := rank_grows P N bounded ux ((mem_positiveInputs P j u).mp mem) negative
  exact below (Nat.succ_le_of_lt grows)

namespace Thermometer

abbrev Word (d : ℕ) := Fin d → Bool

def half (d : ℕ) : ℕ := d / 2

def middle (d : ℕ) : ℕ := (d - 1) / 2

theorem half_le (d : ℕ) : half d ≤ d := by
  unfold half
  omega

theorem middle_le_half (d : ℕ) : middle d ≤ half d := by
  unfold middle half
  omega

theorem split_length {d : ℕ} (positive : 0 < d) :
    middle d + 1 + half d = d := by
  unfold middle half
  omega

theorem half_lt_pow {r d : ℕ} (bound : d < 2^(r+1)) : half d < 2^r := by
  rw [Nat.pow_succ] at bound
  unfold half
  omega

def pivot {d : ℕ} (positive : 0 < d) : Fin d :=
  ⟨middle d,by have eq := split_length positive; omega⟩

def lowerSource {d : ℕ} (i : Fin (half d)) : Fin d :=
  ⟨i.val,i.isLt.trans_le (half_le d)⟩

def upperSource {d : ℕ} (positive : 0 < d) (i : Fin (half d)) : Fin d :=
  ⟨middle d + 1 + i.val,by
    have eq := split_length positive
    have h := i.isLt
    omega⟩

def lowerSlot {d : ℕ} (i : Fin d) (before : i.val < middle d) : Fin (half d) :=
  ⟨i.val,before.trans_le (middle_le_half d)⟩

def upperSlot {d : ℕ} (positive : 0 < d) (i : Fin d) (after : middle d < i.val) : Fin (half d) :=
  ⟨i.val - (middle d + 1),by
    have eq := split_length positive
    have h := i.isLt
    omega⟩

def lowerWord {d : ℕ} (w : Word d) : Word (half d) :=
  fun i => if i.val < middle d then w (lowerSource i) else false

def upperWord {d : ℕ} (positive : 0 < d) (w : Word d) : Word (half d) :=
  fun i => w (upperSource positive i)

def folded {d : ℕ} (positive : 0 < d) (w : Word d) : Word (half d) :=
  fun i => (!w (pivot positive) && lowerWord w i) || upperWord positive w i

private theorem lower_antitone {d : ℕ} {w : Word d} (ordered : Antitone w) :
    Antitone (lowerWord w) := by
  intro i j compare
  by_cases before : j.val < middle d
  · have earlier : i.val < middle d := lt_of_le_of_lt compare before
    simp only [lowerWord,ite_eq_left before,ite_eq_left earlier]
    exact ordered (show lowerSource i ≤ lowerSource j from compare)
  · simp only [lowerWord,ite_eq_right before]
    exact Bool.false_le _

private theorem upper_antitone {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w) :
    Antitone (upperWord positive w) := by
  intro i j compare
  apply ordered
  change middle d + 1 + i.val ≤ middle d + 1 + j.val
  exact Nat.add_le_add_left compare _

theorem folded_eq_lower {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w)
    (off : w (pivot positive) = false) (i : Fin (half d)) :
    folded positive w i = lowerWord w i := by
  have after : pivot positive ≤ upperSource positive i := by
    change middle d ≤ middle d + 1 + i.val
    omega
  have upperOff : upperWord positive w i = false :=
    Bool.eq_false_of_le_false (by simpa only [off,upperWord] using ordered after)
  simp [folded,off,upperOff]

theorem folded_eq_upper {d : ℕ} (positive : 0 < d) {w : Word d}
    (on : w (pivot positive) = true) (i : Fin (half d)) :
    folded positive w i = upperWord positive w i := by
  simp [folded,on]

theorem folded_antitone {d : ℕ} (positive : 0 < d) {w : Word d}
    (ordered : Antitone w) : Antitone (folded positive w) := by
  cases bit : w (pivot positive)
  · rw [funext (folded_eq_lower positive ordered bit)]
    exact lower_antitone ordered
  · rw [funext (folded_eq_upper positive bit)]
    exact upper_antitone positive ordered

def decoded {d : ℕ} (positive : 0 < d) (notPivot : Bool)
    (notHalf : Word (half d)) (i : Fin d) : Bool :=
  if before : i.val < middle d then notPivot && notHalf (lowerSlot i before)
  else if atPivot : i.val = middle d then notPivot
  else notPivot || notHalf (upperSlot positive i (by omega))

theorem decoded_lower {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (before : i.val < middle d) :
    decoded positive b z i = (b && z (lowerSlot i before)) := by
  simp only [decoded,dite_eq_left before]

theorem decoded_pivot {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (atPivot : i.val = middle d) : decoded positive b z i = b := by
  have notBefore : ¬ i.val < middle d := by omega
  simp only [decoded,dite_eq_right notBefore,dite_eq_left atPivot]

theorem decoded_upper {d : ℕ} (positive : 0 < d) (b : Bool) (z : Word (half d))
    (i : Fin d) (after : middle d < i.val) :
    decoded positive b z i = (b || z (upperSlot positive i after)) := by
  have notBefore : ¬ i.val < middle d := by omega
  have notPivot : i.val ≠ middle d := by omega
  simp only [decoded,dite_eq_right notBefore,dite_eq_right notPivot]

private theorem lower_at_slot {d : ℕ} (w : Word d) (i : Fin d)
    (before : i.val < middle d) : lowerWord w (lowerSlot i before) = w i := by
  have same : lowerSource (lowerSlot i before) = i := Fin.ext rfl
  change (if i.val < middle d then w (lowerSource (lowerSlot i before)) else false) = w i
  rw [ite_eq_left before,same]

private theorem upper_at_slot {d : ℕ} (positive : 0 < d) (w : Word d) (i : Fin d)
    (after : middle d < i.val) : upperWord positive w (upperSlot positive i after) = w i := by
  apply congrArg w
  apply Fin.ext
  change middle d + 1 + (i.val - (middle d + 1)) = i.val
  omega

theorem decoded_correct {d : ℕ} (positive : 0 < d) {w : Word d} (ordered : Antitone w)
    {z : Word (half d)} (tail : ∀ j, z j = !(folded positive w j)) (i : Fin d) :
    decoded positive (!w (pivot positive)) z i = !w i := by
  rcases lt_trichotomy i.val (middle d) with before | atPivot | after
  · rw [decoded_lower positive _ _ _ before]
    cases bit : w (pivot positive)
    · simp [bit,tail,folded_eq_lower positive ordered bit,lower_at_slot w i before]
    · have earlier : i ≤ pivot positive := by
        change i.val ≤ middle d
        omega
      have on : w i = true := Bool.eq_true_of_true_le (by simpa only [bit] using ordered earlier)
      simp [bit,on]
  · have same : pivot positive = i := Fin.ext atPivot.symm
    rw [decoded_pivot positive _ _ _ atPivot,same]
  · rw [decoded_upper positive _ _ _ after]
    cases bit : w (pivot positive)
    · have later : pivot positive ≤ i := by
        change middle d ≤ i.val
        omega
      have off : w i = false := Bool.eq_false_of_le_false (by simpa only [bit] using ordered later)
      simp [bit,off]
    · simp [bit,tail,folded_eq_upper positive bit,upper_at_slot positive w i after]

def inverted : (r d : ℕ) → Word d → Word d
  | 0, _, w => w
  | r+1, d, w =>
    if positive : 0 < d then
      decoded positive (!w (pivot positive)) (inverted r (half d) (folded positive w))
    else w

theorem inverted_correct {r d : ℕ} (bound : d < 2^r) (w : Word d) (ordered : Antitone w) :
    inverted r d w = fun i => !w i := by
  induction r generalizing d with
  | zero =>
    funext i
    have existsIndex := i.isLt
    simp at bound
    omega
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inverted,dite_eq_left positive]
      funext i
      have complement := ih (half_lt_pow bound) (folded positive w)
        (folded_antitone positive ordered)
      exact decoded_correct positive ordered (congrFun complement) i
    · funext i
      have existsIndex := i.isLt
      omega

def stepBinary (d : ℕ) : ℕ := 2 * half d + (d - 1)

theorem step_binary_bound (d : ℕ) : stepBinary d + 4 * half d ≤ 4*d := by
  unfold stepBinary half
  omega

def inversionBinary : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r+1, d => if 0 < d then stepBinary d + inversionBinary r (half d) else 0

def inversionNot : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r+1, d => if 0 < d then 1 + inversionNot r (half d) else 0

theorem inversion_binary_bound (r d : ℕ) : inversionBinary r d ≤ 4*d := by
  induction r generalizing d with
  | zero => simp [inversionBinary]
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inversionBinary,ite_eq_left positive]
      exact Nat.le_trans (Nat.add_le_add_left (ih (half d)) _) (step_binary_bound d)
    · simp [inversionBinary,positive]

theorem inversion_not_bound (r d : ℕ) : inversionNot r d ≤ r := by
  induction r generalizing d with
  | zero => simp [inversionNot]
  | succ r ih =>
    by_cases positive : 0 < d
    · rw [inversionNot,ite_eq_left positive]
      have count := ih (half d)
      omega
    · simp [inversionNot,positive]

end Thermometer

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def binaryValue (conjunction x y : Bool) : Bool := if conjunction then x && y else x || y

def appendBinary (conjunction : Bool) (C : Circuit) (left right : ℕ) : Circuit :=
  if conjunction then appendAnd C left right else appendOr C left right

def foldBinary (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ) :
    List ℕ → Circuit × ℕ
  | [] => (C,base)
  | i :: rest => foldBinary n conjunction (appendBinary conjunction C base i) (nextWire n C) rest

private theorem fold_values (conjunction : Bool) (indices : List ℕ) (a b : ℕ → Bool)
    (same : ∀ i ∈ indices, a i = b i) (base : Bool) :
    indices.foldl (fun acc i => binaryValue conjunction acc (a i)) base =
      indices.foldl (fun acc i => binaryValue conjunction acc (b i)) base := by
  induction indices generalizing base with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons,same i (List.mem_cons_self ..)]
    exact ih (fun j hj => same j (List.mem_cons_of_mem _ hj)) _

theorem foldBinary_spec (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ)
    (indices : List ℕ) (basis : FanInTwo C) (reads : ReadsBack n C)
    (baseValid : base < nextWire n C) (valid : ∀ i ∈ indices, i < nextWire n C) :
    let result := foldBinary n conjunction C base indices
    FanInTwo result.1 ∧ ReadsBack n result.1 ∧ result.2 < nextWire n result.1 ∧
      result.1.size = C.size + indices.length ∧ notCount result.1 = notCount C ∧
      ∀ (x : List Bool), x.length = n →
        (∀ i < nextWire n C, value result.1 x i = value C x i) ∧
        value result.1 x result.2 =
          indices.foldl (fun acc i => binaryValue conjunction acc (value C x i)) (value C x base) := by
  induction indices generalizing C base with
  | nil => exact ⟨basis,reads,baseValid,by simp [foldBinary],rfl,fun _ _ => ⟨fun _ _ => rfl,rfl⟩⟩
  | cons i rest ih =>
    let D := appendBinary conjunction C base i
    have iValid := valid i (List.mem_cons_self ..)
    have size : D.size = C.size+1 := by cases conjunction <;> simp [D,appendBinary]
    have nots : notCount D = notCount C := by cases conjunction <;> simp [D,appendBinary]
    have growth : nextWire n D = nextWire n C+1 := by simp [nextWire,size,Nat.add_assoc]
    have forms : FanInTwo D := by
      cases conjunction
      · exact appendOr_fanInTwo basis
      · exact appendAnd_fanInTwo basis
    have previous : ReadsBack n D := by
      cases conjunction
      · exact appendOr_readsBack reads baseValid iValid
      · exact appendAnd_readsBack reads baseValid iValid
    have persist (x : List Bool) (length : x.length = n) (j : ℕ) (earlier : j < nextWire n C) :
        value D x j = value C x j := by
      rw [← length] at earlier
      cases conjunction
      · exact appendGate_old (g := ⟨.or,[base,i]⟩) earlier
      · exact appendGate_old (g := ⟨.and,[base,i]⟩) earlier
    have evaluated (x : List Bool) (length : x.length = n) :
        value D x (nextWire n C) = binaryValue conjunction (value C x base) (value C x i) := by
      rw [← length]
      cases conjunction
      · exact appendOr_new C x base i
      · exact appendAnd_new C x base i
    obtain ⟨hasBasis,hasReads,output,finalSize,finalNot,wires⟩ :=
      ih D (nextWire n C) forms previous (by rw [growth]; omega)
        (fun j hj => (valid j (List.mem_cons_of_mem _ hj)).trans (by rw [growth]; omega))
    refine ⟨hasBasis,hasReads,output,?_,finalNot.trans nots,?_⟩
    · change (foldBinary n conjunction D (nextWire n C) rest).1.size = C.size + (i :: rest).length
      rw [finalSize,size,List.length_cons]
      omega
    · intro x length
      obtain ⟨old,current⟩ := wires x length
      refine ⟨fun j hj => (old j (hj.trans (by rw [growth]; omega))).trans (persist x length j hj),?_⟩
      change value (foldBinary n conjunction D (nextWire n C) rest).1 x
        (foldBinary n conjunction D (nextWire n C) rest).2 =
        (i :: rest).foldl (fun acc j => binaryValue conjunction acc (value C x j)) (value C x base)
      rw [List.foldl_cons,current,evaluated x length]
      exact fold_values conjunction rest (value D x) (value C x)
        (fun j hj => persist x length j (valid j (List.mem_cons_of_mem _ hj))) _

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def withConstants {n : ℕ} (x : Input n) : List Bool := List.ofFn x ++ [false,true]

@[local simp] theorem withConstants_length {n : ℕ} (x : Input n) :
    (withConstants x).length = n+2 := by simp [withConstants]

theorem input_value {n : ℕ} (C : Circuit) (x : Input n) (i : Fin n) :
    value C (withConstants x) i.val = x i := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  have inside : i.val < (List.ofFn x).length := by simpa using i.isLt
  simp only [withConstants,List.getD_eq_getElem?_getD,List.getElem?_append_left inside]
  simp [List.getElem?_ofFn,i.isLt]

theorem false_value {n : ℕ} (C : Circuit) (x : Input n) :
    value C (withConstants x) n = false := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  simp [withConstants,List.getD_eq_getElem?_getD]

theorem true_value {n : ℕ} (C : Circuit) (x : Input n) :
    value C (withConstants x) (n+1) = true := by
  rw [value_input C (withConstants x) (by rw [withConstants_length]; omega)]
  have outside : (List.ofFn x).length ≤ n+1 := by simp
  simp [withConstants,List.getD_eq_getElem?_getD,List.getElem?_append_right outside]

def coneIndices {n : ℕ} (u : Input n) : List ℕ :=
  ((List.finRange n).filter u).map (fun i => i.val)

theorem coneIndices_length {n : ℕ} (u : Input n) : (coneIndices u).length ≤ n := by
  simpa [coneIndices] using List.length_filter_le (p := u) (l := List.finRange n)

private theorem fold_and_true (inputs : List ℕ) (bits : ℕ → Bool) (base : Bool) :
    inputs.foldl (fun b i => b && bits i) base = true ↔
      base = true ∧ ∀ i ∈ inputs, bits i = true := by
  induction inputs generalizing base with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons,ih,Bool.and_eq_true,List.mem_cons,forall_eq_or_imp,and_assoc]

def emitCone {n : ℕ} (C : Circuit) (u : Input n) : Circuit × ℕ :=
  foldBinary (n+2) true C (n+1) (coneIndices u)

theorem emitCone_spec {n : ℕ} (C : Circuit) (u : Input n)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    let result := emitCone C u
    FanInTwo result.1 ∧ ReadsBack (n+2) result.1 ∧ result.2 < nextWire (n+2) result.1 ∧
      C.size ≤ result.1.size ∧ result.1.size ≤ C.size+n ∧ notCount result.1 = notCount C ∧
      (∀ x : Input n, ∀ i < nextWire (n+2) C,
        value result.1 (withConstants x) i = value C (withConstants x) i) ∧
      ∀ x : Input n, value result.1 (withConstants x) result.2 = true ↔ u ≤ x := by
  have validBase : n+1 < nextWire (n+2) C := by unfold nextWire; omega
  have valid : ∀ i ∈ coneIndices u, i < nextWire (n+2) C := by
    intro i hm
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
    unfold nextWire
    omega
  obtain ⟨newBasis,newReads,output,size,neg,sem⟩ :=
    foldBinary_spec (n+2) true C (n+1) (coneIndices u) basis reads validBase valid
  refine ⟨newBasis,newReads,output,(Nat.le_add_right _ _).trans size.ge,size.le.trans
    (Nat.add_le_add_left (coneIndices_length u) _),neg,?_,?_⟩
  · intro x i hi
    exact (sem (withConstants x) (withConstants_length x)).1 i hi
  · intro x
    have evaluated := (sem (withConstants x) (withConstants_length x)).2
    change value (foldBinary (n+2) true C (n+1) (coneIndices u)).1 (withConstants x)
        (foldBinary (n+2) true C (n+1) (coneIndices u)).2 = true ↔ u ≤ x
    rw [evaluated,true_value]
    simp only [binaryValue,ite_true,fold_and_true,true_and]
    rw [cone_iff]
    constructor
    · intro every i active
      have mem : i.val ∈ coneIndices u := List.mem_map.mpr
        ⟨i,List.mem_filter.mpr ⟨List.mem_finRange _,active⟩,rfl⟩
      exact (input_value C x i).symm.trans (every i.val mem)
    · intro above i mem
      obtain ⟨j,selected,rfl⟩ := List.mem_map.mp mem
      exact (input_value C x j).trans (above j (List.mem_filter.mp selected).2)

def emitCones {n : ℕ} (C : Circuit) : List (Input n) → Circuit × List ℕ
  | [] => (C,[])
  | u :: rest =>
    let first := emitCone C u
    let later := emitCones first.1 rest
    (later.1,first.2 :: later.2)

theorem emitCones_spec {n : ℕ} (C : Circuit) (words : List (Input n))
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    let result := emitCones C words
    FanInTwo result.1 ∧ ReadsBack (n+2) result.1 ∧ C.size ≤ result.1.size ∧
      result.1.size ≤ C.size+n*words.length ∧ notCount result.1 = notCount C ∧
      (∀ x : Input n, ∀ i < nextWire (n+2) C,
        value result.1 (withConstants x) i = value C (withConstants x) i) ∧
      List.Forall₂ (fun u i => i < nextWire (n+2) result.1 ∧
        ∀ x : Input n, value result.1 (withConstants x) i = true ↔ u ≤ x) words result.2 := by
  induction words generalizing C with
  | nil => exact ⟨basis,reads,le_rfl,by simp [emitCones],rfl,fun _ _ _ => rfl,.nil⟩
  | cons u rest ih =>
    let first := emitCone C u
    let later := emitCones first.1 rest
    obtain ⟨headBasis,headReads,headWire,growth,headCost,headNot,headOld,headValue⟩ :=
      emitCone_spec C u basis reads
    obtain ⟨tailBasis,tailReads,tailGrowth,tailCost,tailNot,tailOld,tailValues⟩ :=
      ih first.1 headBasis headReads
    have headValid : first.2 < nextWire (n+2) later.1 := by
      exact headWire.trans_le (Nat.add_le_add_left tailGrowth (n+2))
    refine ⟨tailBasis,tailReads,growth.trans tailGrowth,?_,tailNot.trans headNot,?_,?_⟩
    · change later.1.size ≤ C.size + n * (u :: rest).length
      rw [List.length_cons,Nat.mul_succ]
      change later.1.size ≤ first.1.size + n*rest.length at tailCost
      change first.1.size ≤ C.size+n at headCost
      omega
    · intro x i hi
      have through : i < nextWire (n+2) first.1 :=
        hi.trans_le (Nat.add_le_add_left growth (n+2))
      exact (tailOld x i through).trans (headOld x i hi)
    · refine .cons ⟨headValid,?_⟩ tailValues
      intro x
      change value later.1 (withConstants x) first.2 = true ↔ u ≤ x
      rw [tailOld x first.2 headWire]
      exact headValue x

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def appendGates (C : Circuit) (gates : List Gate) : Circuit := ⟨C.gates ++ gates, C.output⟩

def appendFamily {k : Nat} (C : Circuit) (gate : Fin k → Gate) : Circuit :=
  appendGates C (List.ofFn gate)

private theorem appendGates_cons (C : Circuit) (g : Gate) (rest : List Gate) :
    appendGates C (g :: rest) = appendGates (appendGate C g) rest := by
  simp [appendGates,appendGate,List.append_assoc]

theorem appendGates_prefix (C : Circuit) (gates : List Gate) : C.gates <+: (appendGates C gates).gates :=
  ⟨gates,rfl⟩

@[local simp] theorem appendGates_size (C : Circuit) (gates : List Gate) :
    (appendGates C gates).size = C.size + gates.length := by
  simp [appendGates,Circuit.size]

@[local simp] theorem appendGates_nextWire (n : Nat) (C : Circuit) (gates : List Gate) :
    nextWire n (appendGates C gates) = nextWire n C + gates.length := by
  simp [nextWire,Nat.add_assoc]

@[local simp] theorem appendGates_output (C : Circuit) (gates : List Gate) :
    (appendGates C gates).output = C.output := rfl

theorem appendGates_notCount (C : Circuit) (gates : List Gate) :
    notCount (appendGates C gates) =
      notCount C + (gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)).length := by
  simp [notCount,appendGates]

theorem appendGates_notCount_eq {C : Circuit} {gates : List Gate}
    (noNot : ∀ g ∈ gates, g.op ≠ .not) : notCount (appendGates C gates) = notCount C := by
  have empty : (gates.filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)) = [] :=
    List.filter_eq_nil_iff.mpr fun g member => by simp [noNot g member]
  simp [appendGates_notCount,empty]

private abbrev GateShape (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem appendGates_fanInTwo {C : Circuit} {gates : List Gate} (basis : FanInTwo C)
    (shape : ∀ g ∈ gates, GateShape g) : FanInTwo (appendGates C gates) := by
  intro g member
  rcases List.mem_append.mp member with old | added
  · exact basis g old
  · exact shape g added

theorem appendGates_readsBack {n : Nat} {C : Circuit} {gates : List Gate} (valid : ReadsBack n C)
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire n C) : ReadsBack n (appendGates C gates) := by
  induction gates generalizing C with
  | nil => simpa [appendGates] using valid
  | cons g rest ih =>
    rw [appendGates_cons]
    have fits : ∀ i ∈ g.inputs, i < nextWire n C := reads g (List.mem_cons_self ..)
    apply ih (appendGate_readsBack valid fits)
    intro h member i input
    exact Nat.lt_of_lt_of_le (reads h (List.mem_cons_of_mem _ member) i input)
      (nextWire_le_of_prefix (appendGate_prefix C g))

theorem appendGates_old {C : Circuit} {gates : List Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendGates C gates) x i = value C x i :=
  value_of_prefix (appendGates_prefix C gates) valid

private def readGate (C : Circuit) (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map (value C x))

private theorem appendGates_wires {C : Circuit} {gates : List Gate} {x : List Bool}
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire x.length C) :
    (appendGates C gates).wires x = C.wires x ++ gates.map (readGate C x) := by
  induction gates generalizing C with
  | nil => simp [appendGates]
  | cons g rest ih =>
    have restReads : ∀ h ∈ rest, ∀ i ∈ h.inputs, i < nextWire x.length (appendGate C g) :=
      fun h member i input => Nat.lt_of_lt_of_le (reads h (List.mem_cons_of_mem _ member) i input)
        (nextWire_le_of_prefix (appendGate_prefix C g))
    have tail : rest.map (readGate (appendGate C g) x) = rest.map (readGate C x) := by
      apply List.map_congr_left
      intro h member
      unfold readGate
      apply congrArg h.op.eval
      apply List.map_congr_left
      intro i input
      exact appendGate_old (g := g) (reads h (List.mem_cons_of_mem _ member) i input)
    rw [appendGates_cons,ih restReads,tail,appendGate_wires]
    simp [List.append_assoc,readGate]

theorem appendGates_new {C : Circuit} {gates : List Gate} {x : List Bool}
    (reads : ∀ g ∈ gates, ∀ i ∈ g.inputs, i < nextWire x.length C) (j : Fin gates.length) :
    value (appendGates C gates) x (nextWire x.length C + j.val) =
      gates[j].op.eval (gates[j].inputs.map (value C x)) := by
  change ((appendGates C gates).wires x).getD (nextWire x.length C + j.val) false = _
  rw [appendGates_wires (x := x) reads]
  have within : (C.wires x).length ≤ nextWire x.length C + j.val := by rw [wires_length]; omega
  have index : nextWire x.length C + j.val - nextWire x.length C = j.val := by omega
  rw [List.getD_append_right _ _ _ _ within,wires_length,index]
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem j.isLt,readGate]

theorem appendFamily_prefix {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    C.gates <+: (appendFamily C gate).gates := appendGates_prefix C _

@[local simp] theorem appendFamily_size {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    (appendFamily C gate).size = C.size + k := by simp [appendFamily]

@[local simp] theorem appendFamily_nextWire {k : Nat} (n : Nat) (C : Circuit) (gate : Fin k → Gate) :
    nextWire n (appendFamily C gate) = nextWire n C + k := by simp [appendFamily]

@[local simp] theorem appendFamily_output {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    (appendFamily C gate).output = C.output := rfl

theorem appendFamily_notCount {k : Nat} (C : Circuit) (gate : Fin k → Gate) :
    notCount (appendFamily C gate) = notCount C +
      ((List.ofFn gate).filter fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not)).length :=
  appendGates_notCount C _

theorem appendFamily_notCount_eq {k : Nat} {C : Circuit} {gate : Fin k → Gate}
    (noNot : ∀ j, (gate j).op ≠ .not) : notCount (appendFamily C gate) = notCount C := by
  apply appendGates_notCount_eq
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact noNot j

theorem appendFamily_fanInTwo {k : Nat} {C : Circuit} {gate : Fin k → Gate} (basis : FanInTwo C)
    (shape : ∀ j, GateShape (gate j)) : FanInTwo (appendFamily C gate) := by
  apply appendGates_fanInTwo basis
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact shape j

theorem appendFamily_readsBack {k n : Nat} {C : Circuit} {gate : Fin k → Gate}
    (valid : ReadsBack n C) (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire n C) :
    ReadsBack n (appendFamily C gate) := by
  apply appendGates_readsBack valid
  intro g member
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  exact reads j

theorem appendFamily_old {k : Nat} {C : Circuit} {gate : Fin k → Gate} {x : List Bool} {i : Nat}
    (valid : i < nextWire x.length C) : value (appendFamily C gate) x i = value C x i :=
  appendGates_old valid

theorem appendFamily_new {k : Nat} {C : Circuit} {gate : Fin k → Gate} {x : List Bool}
    (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire x.length C) (j : Fin k) :
    value (appendFamily C gate) x (nextWire x.length C + j.val) =
      (gate j).op.eval ((gate j).inputs.map (value C x)) := by
  have readsList : ∀ g ∈ List.ofFn gate, ∀ i ∈ g.inputs, i < nextWire x.length C := by
    intro g member
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp member
    exact reads t
  let t : Fin (List.ofFn gate).length := ⟨j.val,by simpa using j.isLt⟩
  simpa [appendFamily,t] using appendGates_new readsList t

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem appendBinary_prefix (conjunction : Bool) (C : Circuit) (a b : ℕ) :
    C.gates <+: (appendBinary conjunction C a b).gates := by
  cases conjunction
  · exact appendGate_prefix C ⟨.or,[a,b]⟩
  · exact appendGate_prefix C ⟨.and,[a,b]⟩

theorem foldBinary_prefix (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ) (indices : List ℕ) :
    C.gates <+: (foldBinary n conjunction C base indices).1.gates := by
  induction indices generalizing C base with
  | nil => exact List.prefix_refl _
  | cons i rest ih =>
    exact (appendBinary_prefix conjunction C base i).trans (ih _ _)

theorem foldBinary_size_exact (n : ℕ) (conjunction : Bool) (C : Circuit) (base : ℕ)
    (indices : List ℕ) : (foldBinary n conjunction C base indices).1.size = C.size + indices.length := by
  induction indices generalizing C base with
  | nil => simp [foldBinary]
  | cons i rest ih =>
    have step : (appendBinary conjunction C base i).size = C.size + 1 := by
      cases conjunction <;> simp [appendBinary]
    rw [foldBinary,ih,step,List.length_cons]
    omega

theorem emitCone_prefix {n : ℕ} (C : Circuit) (u : Input n) :
    C.gates <+: (emitCone C u).1.gates := foldBinary_prefix _ _ _ _ _

theorem emitCone_size_exact {n : ℕ} (C : Circuit) (u : Input n) :
    (emitCone C u).1.size = C.size + (coneIndices u).length := foldBinary_size_exact _ _ _ _ _

theorem emitCones_prefix {n : ℕ} (C : Circuit) (words : List (Input n)) :
    C.gates <+: (emitCones C words).1.gates := by
  induction words generalizing C with
  | nil => exact List.prefix_refl _
  | cons u rest ih => exact (emitCone_prefix C u).trans (ih (emitCone C u).1)

theorem emitCones_size_exact {n : ℕ} (C : Circuit) (words : List (Input n)) :
    (emitCones C words).1.size = C.size + (words.map (fun u => (coneIndices u).length)).sum := by
  induction words generalizing C with
  | nil => simp [emitCones]
  | cons u rest ih =>
    change (emitCones (emitCone C u).1 rest).1.size = C.size + _
    rw [ih,emitCone_size_exact,List.map_cons,List.sum_cons]
    omega

theorem supportConeTable {n m : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    ∃ (D : Circuit) (wire : {u : Input n // u ∈ support P N} → ℕ),
      C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ C.size + n*(support P N).card ∧ notCount D = notCount C ∧
      ∀ u, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u.val ≤ x := by
  classical
  let words := (support P N).toList
  let result := emitCones C words
  obtain ⟨newBasis,newReads,_,cost,neg,_,paired⟩ := emitCones_spec C words basis reads
  have available (u : {u : Input n // u ∈ support P N}) :
      ∃ i, i < nextWire (n+2) result.1 ∧
        ∀ x : Input n, value result.1 (withConstants x) i = true ↔ u.val ≤ x := by
    have member : u.val ∈ words := Finset.mem_toList.mpr u.property
    obtain ⟨j,point⟩ := List.mem_iff_get.mp member
    let k : Fin result.2.length := ⟨j.val,by rw [← paired.length_eq]; exact j.isLt⟩
    refine ⟨result.2.get k,?_⟩
    have atIndex := paired.get j.isLt k.isLt
    change result.2.get k < nextWire (n+2) result.1 ∧
      (∀ x : Input n, value result.1 (withConstants x) (result.2.get k) = true ↔ words.get j ≤ x) at atIndex
    simpa only [point] using atIndex
  refine ⟨result.1,fun u => (available u).choose,emitCones_prefix C words,newBasis,newReads,?_,neg,?_⟩
  · simpa only [words,Finset.length_toList] using cost
  · intro u
    exact (available u).choose_spec

theorem supportConeTable_total {n m : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) :
    ∃ (D : Circuit) (wire : Input n → ℕ), C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ C.size + n*(support P N).card ∧ notCount D = notCount C ∧
      (∀ u ∈ support P N, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u ≤ x) ∧
      ∀ u ∉ support P N, wire u = n := by
  classical
  obtain ⟨D,w,extension,newBasis,newReads,cost,neg,semantic⟩ := supportConeTable P N C basis reads
  let wire (u : Input n) : ℕ := if h : u ∈ support P N then w ⟨u,h⟩ else n
  refine ⟨D,wire,extension,newBasis,newReads,cost,neg,?_,?_⟩
  · intro u member
    simpa [wire,member] using semantic ⟨u,member⟩
  · intro u absent
    simp [wire,absent]

theorem supportConeTable_empty {n m : ℕ} (P N : Input n → Fin m → Prop) :
    ∃ (D : Circuit) (wire : Input n → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧
      D.size ≤ n*(support P N).card ∧ notCount D = 0 ∧
      (∀ u ∈ support P N, wire u < nextWire (n+2) D ∧
        ∀ x : Input n, value D (withConstants x) (wire u) = true ↔ u ≤ x) ∧
      ∀ u ∉ support P N, wire u = n := by
  obtain ⟨D,w,_,basis,reads,cost,neg,semantic,defaultWire⟩ :=
    supportConeTable_total P N emptyCircuit emptyCircuit_fanInTwo (emptyCircuit_readsBack (n+2))
  exact ⟨D,w,basis,reads,by simpa using cost,by simpa using neg,semantic,defaultWire⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem fold_or_true (indices : List ℕ) (bits : ℕ → Bool) (base : Bool) :
    indices.foldl (fun b i => b || bits i) base = true ↔
      base = true ∨ ∃ i ∈ indices, bits i = true := by
  induction indices generalizing base with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons,ih,Bool.or_eq_true_iff]
    constructor
    · rintro ((on | on) | ⟨j,mem,on⟩)
      · exact Or.inl on
      · exact Or.inr ⟨i,List.mem_cons_self ..,on⟩
      · exact Or.inr ⟨j,List.mem_cons_of_mem _ mem,on⟩
    · rintro (on | ⟨j,mem,on⟩)
      · exact Or.inl (Or.inl on)
      · rcases List.mem_cons.mp mem with rfl | restMem
        · exact Or.inl (Or.inr on)
        · exact Or.inr ⟨j,restMem,on⟩

theorem append_or_rows {n k : ℕ} (C : Circuit) (rows : Fin k → List ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (rowValid : ∀ i a, a ∈ rows i → a < nextWire (n+2) C) :
    ∃ (D : Circuit) (out : Fin k → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size = C.size + (∑ i : Fin k, (rows i).length) ∧
      (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔
        ∃ a ∈ rows i, value C (withConstants x) a = true := by
  induction k generalizing C with
  | zero =>
    exact ⟨C,Fin.elim0,basis,reads,List.prefix_rfl,rfl,by simp,fun i => Fin.elim0 i,
      fun _ i => Fin.elim0 i⟩
  | succ k ih =>
    let first := foldBinary (n+2) false C n (rows 0)
    have zeroLive : n < nextWire (n+2) C := by unfold nextWire; omega
    obtain ⟨hBasis,hReads,hLive,hSize,hNot,hEval⟩ :=
      foldBinary_spec (n+2) false C n (rows 0) basis reads zeroLive (rowValid 0)
    have firstPrefix : C.gates <+: first.1.gates := by
      unfold first
      apply foldBinary_prefix
    have tailValid (i : Fin k) (a : ℕ) (ha : a ∈ rows i.succ) :
        a < nextWire (n+2) first.1 :=
      (rowValid i.succ a ha).trans_le (nextWire_le_of_prefix firstPrefix)
    obtain ⟨D,tail,dBasis,dReads,dPrefix,dNot,dSize,dLive,dEval⟩ :=
      ih first.1 (fun i => rows i.succ) hBasis hReads tailValid
    let out : Fin (k+1) → ℕ := Fin.cases first.2 tail
    refine ⟨D,out,dBasis,dReads,firstPrefix.trans dPrefix,dNot.trans hNot,?_,?_,?_⟩
    · rw [dSize,Fin.sum_univ_succ]
      change first.1.size = C.size + (rows 0).length at hSize
      rw [hSize,Nat.add_assoc]
    · intro i
      refine Fin.cases ?_ (fun j => dLive j) i
      exact hLive.trans_le (nextWire_le_of_prefix dPrefix)
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · change value D (withConstants x) first.2 = true ↔ _
        have live : first.2 < nextWire (withConstants x).length first.1 := by
          simpa only [withConstants_length] using hLive
        rw [value_of_prefix dPrefix live]
        change value (foldBinary (n+2) false C n (rows 0)).1 (withConstants x)
          (foldBinary (n+2) false C n (rows 0)).2 = true ↔ _
        rw [(hEval (withConstants x) (withConstants_length x)).2,false_value]
        simp only [binaryValue,Bool.false_eq_true,ite_false,fold_or_true,false_or]
      · change value D (withConstants x) (tail j) = true ↔ _
        rw [dEval x j]
        constructor <;> rintro ⟨a,mem,on⟩
        · exact ⟨a,mem,((hEval (withConstants x) (withConstants_length x)).1 a
            (rowValid j.succ a mem)).symm.trans on⟩
        · exact ⟨a,mem,((hEval (withConstants x) (withConstants_length x)).1 a
            (rowValid j.succ a mem)).trans on⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private theorem value_prefix_input {n : ℕ} {C D : Circuit}
    (extension : C.gates <+: D.gates) (x : Input n) {i : ℕ} (live : i < nextWire (n+2) C) :
    value D (withConstants x) i = value C (withConstants x) i :=
  value_of_prefix extension (by simpa only [withConstants_length] using live)

theorem append_suffix_or {n k : ℕ} (C : Circuit) (bucket : Fin k → ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C) (live : ∀ i, bucket i < nextWire (n+2) C) :
    ∃ (D : Circuit) (out : Fin k → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size = C.size+k ∧ (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔
        ∃ j : Fin k, i ≤ j ∧ value C (withConstants x) (bucket j) = true := by
  induction k generalizing C with
  | zero => exact ⟨C,Fin.elim0,basis,reads,List.prefix_rfl,rfl,by simp,fun i => Fin.elim0 i,
      fun _ i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨B,tail,bBasis,bReads,bPrefix,bNot,bSize,bLive,bEval⟩ :=
      ih C (fun j => bucket j.succ) basis reads (fun j => live j.succ)
    let lower := if reaches : 0 < k then tail ⟨0,reaches⟩ else n
    have lowerLive : lower < nextWire (n+2) B := by
      unfold lower
      split
      · exact bLive _
      · unfold nextWire
        omega
    have lowerEval (x : Input n) : value B (withConstants x) lower = true ↔
        ∃ j : Fin k, value C (withConstants x) (bucket j.succ) = true := by
      unfold lower
      split
      · rename_i positive
        rw [bEval x ⟨0,positive⟩]
        constructor
        · rintro ⟨j,_,on⟩
          exact ⟨j,on⟩
        · rintro ⟨j,on⟩
          exact ⟨j,show (0 : ℕ) ≤ j.val from Nat.zero_le _,on⟩
      · rename_i empty
        rw [false_value]
        constructor
        · intro impossible
          contradiction
        · rintro ⟨j,_⟩
          exact (empty (Nat.zero_lt_of_lt j.isLt)).elim
    let D := appendOr B (bucket 0) lower
    let out : Fin (k+1) → ℕ := Fin.cases (nextWire (n+2) B) tail
    have headLive := (live 0).trans_le (nextWire_le_of_prefix bPrefix)
    have lastPrefix : B.gates <+: D.gates := appendGate_prefix _ _
    have wireGrowth : nextWire (n+2) D = nextWire (n+2) B + 1 := nextWire_appendGate _ _ _
    refine ⟨D,out,appendOr_fanInTwo bBasis,appendOr_readsBack bReads headLive lowerLive,
      bPrefix.trans lastPrefix,(appendOr_notCount _ _ _).trans bNot,?_,?_,?_⟩
    · change (appendOr B (bucket 0) lower).size = C.size + (k+1)
      rw [appendOr_size,bSize,Nat.add_assoc]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change nextWire (n+2) B < nextWire (n+2) D
        omega
      · exact (bLive j).trans_le (nextWire_le_of_prefix lastPrefix)
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · change value D (withConstants x) (nextWire (n+2) B) = true ↔
          ∃ j : Fin (k+1), 0 ≤ j ∧ value C (withConstants x) (bucket j) = true
        have evaluated := appendOr_new B (withConstants x) (bucket 0) lower
        simp only [withConstants_length] at evaluated
        rw [show value D (withConstants x) (nextWire (n+2) B) = _ from evaluated,
          Bool.or_eq_true_iff,value_prefix_input bPrefix x (live 0),lowerEval x]
        constructor
        · rintro (head | ⟨j,tailOn⟩)
          · exact ⟨0,le_rfl,head⟩
          · exact ⟨j.succ,show (0 : ℕ) ≤ j.succ.val from Nat.zero_le _,tailOn⟩
        · rintro ⟨j,_,on⟩
          refine Fin.cases ?_ (fun q => ?_) j on
          · exact Or.inl
          · intro tailOn
            exact Or.inr ⟨q,tailOn⟩
      · change value D (withConstants x) (tail j) = true ↔ _
        rw [value_prefix_input lastPrefix x (bLive j),bEval x j]
        constructor
        · rintro ⟨i,order,on⟩
          exact ⟨i.succ,Fin.succ_le_succ_iff.mpr order,on⟩
        · rintro ⟨i,order,on⟩
          refine Fin.cases ?_ (fun q => ?_) i order on
          · intro incompatible _
            change j.val+1 ≤ 0 at incompatible
            omega
          · intro comparable active
            exact ⟨q,Fin.succ_le_succ_iff.mp comparable,active⟩

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private noncomputable def bucketRows {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ)
    (cone : Input n → ℕ) (i : Fin d) : List ℕ :=
  (rankBucket P N d (i.val+1)).toList.map cone

private theorem positive_bucket_cost {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ)
    (cone : Input n → ℕ) :
    (∑ i : Fin d, (bucketRows P N d cone i).length) ≤ (support P N).card := by
  have total : (∑ i : Fin (d+1), (rankBucket P N d i.val).card) = (support P N).card :=
    (Fin.sum_univ_eq_sum_range (fun k => (rankBucket P N d k).card) (d+1)).trans (rank_bucket_count P N d)
  rw [Fin.sum_univ_succ] at total
  have bound : (∑ i : Fin d, (rankBucket P N d (i.val+1)).card) ≤ (support P N).card :=
    (Nat.le_add_left _ _).trans total.le
  simpa [bucketRows] using bound

theorem append_thresholds {n m : ℕ} (P N : Input n → Fin m → Prop) (d : ℕ) (C : Circuit)
    (cone : Input n → ℕ) (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (coneLive : ∀ u ∈ support P N, cone u < nextWire (n+2) C)
    (coneValue : ∀ u ∈ support P N, ∀ x : Input n,
      value C (withConstants x) (cone u) = true ↔ u ≤ x) :
    ∃ (D : Circuit) (out : Fin d → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size ≤ C.size+(support P N).card+d ∧
      (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔ i.val+1 ≤ rank P N d x := by
  let rows := bucketRows P N d cone
  have liveRows (i : Fin d) (a : ℕ) (hm : a ∈ rows i) : a < nextWire (n+2) C := by
    obtain ⟨u,mem,rfl⟩ := List.mem_map.mp hm
    exact coneLive u ((mem_rankBucket P N d (i.val+1) u).mp (Finset.mem_toList.mp mem)).1
  obtain ⟨B,bucket,bBasis,bReads,bPrefix,bNot,bSize,bLive,bEval⟩ :=
    append_or_rows C rows basis reads liveRows
  have bucketEval (x : Input n) (i : Fin d) :
      value B (withConstants x) (bucket i) = true ↔ ∃ u ∈ rankBucket P N d (i.val+1), u ≤ x := by
    rw [bEval x i]
    constructor
    · rintro ⟨a,found,on⟩
      obtain ⟨u,mem,rfl⟩ := List.mem_map.mp found
      have occurrence := Finset.mem_toList.mp mem
      have original := ((mem_rankBucket P N d (i.val+1) u).mp occurrence).1
      exact ⟨u,occurrence,(coneValue u original x).mp on⟩
    · rintro ⟨u,mem,ux⟩
      have original := ((mem_rankBucket P N d (i.val+1) u).mp mem).1
      exact ⟨cone u,List.mem_map.mpr ⟨u,Finset.mem_toList.mpr mem,rfl⟩,
        (coneValue u original x).mpr ux⟩
  obtain ⟨D,out,dBasis,dReads,dPrefix,dNot,dSize,dLive,dEval⟩ :=
    append_suffix_or B bucket bBasis bReads bLive
  refine ⟨D,out,dBasis,dReads,bPrefix.trans dPrefix,dNot.trans bNot,?_,dLive,?_⟩
  · have budget : (∑ i : Fin d, (rows i).length) ≤ (support P N).card :=
      positive_bucket_cost P N d cone
    rw [dSize,bSize]
    omega
  · intro x i
    rw [dEval x i,threshold_buckets P N d (by omega : 0 < i.val+1) x]
    constructor
    · rintro ⟨j,ij,on⟩
      have below : i.val ≤ j.val := ij
      obtain ⟨u,mem,ux⟩ := (bucketEval x j).mp on
      exact ⟨j.val+1,by omega,by omega,u,mem,ux⟩
    · rintro ⟨k,ik,kd,u,mem,ux⟩
      let j : Fin d := ⟨k-1,by omega⟩
      have level : j.val+1 = k := by dsimp [j]; omega
      refine ⟨j,show i.val ≤ j.val from by omega,(bucketEval x j).mpr ?_⟩
      rw [level]
      exact ⟨u,mem,ux⟩

theorem threshold_antitone {n m d : ℕ} {P N : Input n → Fin m → Prop} {D : Circuit}
    {out : Fin d → ℕ}
    (sem : ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔ i.val+1 ≤ rank P N d x)
    (x : Input n) : Antitone (fun i => value D (withConstants x) (out i)) := by
  intro i j ij
  change value D (withConstants x) (out j) ≤ value D (withConstants x) (out i)
  have below : i.val ≤ j.val := ij
  cases high : value D (withConstants x) (out j)
  · simp
  · have low : value D (withConstants x) (out i) = true :=
      (sem x i).mpr (by have reach := (sem x j).mp high; omega)
    rw [low]

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)
open Thermometer (half middle pivot lowerSource upperSource lowerSlot upperSlot
  lowerWord upperWord folded folded_antitone decoded decoded_lower decoded_pivot decoded_upper
  decoded_correct half_lt_pow)

private theorem old_value {n : ℕ} {C D : Circuit} (ext : C.gates <+: D.gates)
    {x : List Bool} (length : x.length = n) {w : ℕ} (live : w < nextWire n C) :
    value D x w = value C x w :=
  value_of_prefix ext (by simpa only [length] using live)

private theorem pair_reads {n : ℕ} {C : Circuit} {a b : ℕ}
    (la : a < nextWire n C) (lb : b < nextWire n C) :
    ∀ i ∈ [a,b], i < nextWire n C := by
  intro i member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact la
  · exact lb

private theorem family_value {k n : ℕ} {C : Circuit} {gate : Fin k → Gate}
    (reads : ∀ j i, i ∈ (gate j).inputs → i < nextWire n C)
    (x : List Bool) (length : x.length = n) (j : Fin k) :
    value (appendFamily C gate) x (nextWire n C + j.val) =
      (gate j).op.eval ((gate j).inputs.map (value C x)) := by
  have valid : ∀ a b, b ∈ (gate a).inputs → b < nextWire x.length C := by
    rw [length]
    exact reads
  simpa only [length] using appendFamily_new (C := C) (gate := gate) (x := x) valid j

set_option maxHeartbeats 1700000 in
private theorem fold_taps {X : Type*} (input : X → List Bool) {n d : ℕ}
    (length : ∀ x, (input x).length = n) (positive : 0 < d) {C : Circuit}
    (fan : FanInTwo C) (back : ReadsBack n C)
    (falseWire : ℕ) (falseLive : falseWire < nextWire n C)
    (falseValue : ∀ x, value C (input x) falseWire = false)
    (taps : Fin d → ℕ) (live : ∀ i, taps i < nextWire n C) :
    ∃ (D : Circuit) (pivotWire : ℕ) (wires : Fin (half d) → ℕ),
      C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack n D ∧
      pivotWire < nextWire n D ∧ (∀ i, wires i < nextWire n D) ∧
      (∀ x, value D (input x) pivotWire = !value C (input x) (taps (pivot positive))) ∧
      (∀ x i, value D (input x) (wires i) =
        folded positive (fun j => value C (input x) (taps j)) i) ∧
      D.size = C.size + 1 + 2 * half d ∧ notCount D = notCount C + 1 := by
  let C0 := appendNot C (taps (pivot positive))
  let b := nextWire n C
  let low (i : Fin (half d)) := if i.val < middle d then taps (lowerSource i) else falseWire
  let ands (i : Fin (half d)) : Gate := ⟨.and,[b,low i]⟩
  let C1 := appendFamily C0 ands
  let mask (i : Fin (half d)) := nextWire n C0 + i.val
  let ors (i : Fin (half d)) : Gate := ⟨.or,[mask i,taps (upperSource positive i)]⟩
  let C2 := appendFamily C1 ors
  let output (i : Fin (half d)) := nextWire n C1 + i.val
  have e0 : C.gates <+: C0.gates := appendGate_prefix C _
  have e1 : C0.gates <+: C1.gates := appendFamily_prefix C0 ands
  have e2 : C1.gates <+: C2.gates := appendFamily_prefix C1 ors
  have e01 := e0.trans e1
  have e012 := e01.trans e2
  have bLive : b < nextWire n C0 := by
    simp [b,C0,appendNot]
  have lowLive (i : Fin (half d)) : low i < nextWire n C0 := by
    apply Nat.lt_of_lt_of_le _ (nextWire_le_of_prefix e0)
    unfold low
    split
    · exact live _
    · exact falseLive
  have andReads : ∀ j i, i ∈ (ands j).inputs → i < nextWire n C0 :=
    fun j => pair_reads bLive (lowLive j)
  have maskLive (i : Fin (half d)) : mask i < nextWire n C1 := by
    simpa only [mask,C1,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
  have orReads : ∀ j i, i ∈ (ors j).inputs → i < nextWire n C1 :=
    fun j => pair_reads (maskLive j) ((live _).trans_le (nextWire_le_of_prefix e01))
  have f0 : FanInTwo C0 := appendNot_fanInTwo fan
  have f1 : FanInTwo C1 := appendFamily_fanInTwo (gate := ands) f0 (by
    intro j
    change GateOp.and ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      ([b,low j] : List ℕ).length ≤ 2
    simp)
  have f2 : FanInTwo C2 := appendFamily_fanInTwo (gate := ors) f1 (by
    intro j
    change GateOp.or ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
      ([mask j,taps (upperSource positive j)] : List ℕ).length ≤ 2
    simp)
  have r0 : ReadsBack n C0 := appendNot_readsBack back (live (pivot positive))
  have r1 : ReadsBack n C1 := appendFamily_readsBack r0 andReads
  have r2 : ReadsBack n C2 := appendFamily_readsBack r1 orReads
  have atPivot (x : X) : value C0 (input x) b = !value C (input x) (taps (pivot positive)) := by
    simpa only [C0,b,length x] using appendNot_new C (input x) (taps (pivot positive))
  have foldOn (x : X) (i : Fin (half d)) : value C2 (input x) (output i) =
      folded positive (fun j => value C (input x) (taps j)) i := by
    let w : Fin d → Bool := fun j => value C (input x) (taps j)
    have lowOn : value C0 (input x) (low i) = lowerWord w i := by
      by_cases before : i.val < middle d
      · simp only [low,lowerWord,ite_eq_left before]
        exact old_value e0 (length x) (live (lowerSource i))
      · simp only [low,lowerWord,ite_eq_right before]
        exact (old_value e0 (length x) falseLive).trans (falseValue x)
    have maskOn : value C1 (input x) (mask i) = (!w (pivot positive) && lowerWord w i) := by
      have eq := family_value (gate := ands) andReads (input x) (length x) i
      simpa [C1,mask,ands,GateOp.eval,atPivot x,lowOn,w] using eq
    have upperOn : value C1 (input x) (taps (upperSource positive i)) = upperWord positive w i :=
      old_value e01 (length x) (live (upperSource positive i))
    have eq := family_value (gate := ors) orReads (input x) (length x) i
    simpa [C2,output,ors,GateOp.eval,maskOn,upperOn,folded,w] using eq
  refine ⟨C2,b,output,e012,f2,r2,bLive.trans_le (nextWire_le_of_prefix (e1.trans e2)),
    ?_,?_,foldOn,?_,?_⟩
  · intro i
    simpa only [output,C2,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
  · intro x
    exact (old_value (e1.trans e2) (length x) bLive).trans (atPivot x)
  · dsimp only [C2,C1,C0]
    simp only [appendFamily_size,appendNot_size]
    omega
  · rw [show C2 = appendFamily C1 ors from rfl,
      appendFamily_notCount_eq (gate := ors) (by intro j; simp [ors]),
      show C1 = appendFamily C0 ands from rfl,
      appendFamily_notCount_eq (gate := ands) (by intro j; simp [ands])]
    simp [C0]

private def decoderGates {d : ℕ} (positive : 0 < d) (b falseWire : ℕ)
    (tail : Fin (half d) → ℕ) (i : Fin d) : Gate :=
  if before : i.val < middle d then ⟨.and,[b,tail (lowerSlot i before)]⟩
  else if eq : i.val = middle d then ⟨.or,[b,falseWire]⟩
  else ⟨.or,[b,tail (upperSlot positive i (by omega))]⟩

private theorem decoder_reads {n d : ℕ} (positive : 0 < d) {C : Circuit} {b f : ℕ}
    {tail : Fin (half d) → ℕ} (liveB : b < nextWire n C) (liveF : f < nextWire n C)
    (liveTail : ∀ j, tail j < nextWire n C) :
    ∀ j i, i ∈ (decoderGates positive b f tail j).inputs → i < nextWire n C := by
  intro j i member
  unfold decoderGates at member
  split at member
  · exact pair_reads liveB (liveTail _) i member
  · split at member
    · exact pair_reads liveB liveF i member
    · exact pair_reads liveB (liveTail _) i member

private theorem decoder_value {d : ℕ} (positive : 0 < d) (C : Circuit) (x : List Bool)
    (b f : ℕ) (tail : Fin (half d) → ℕ) (off : value C x f = false) (i : Fin d) :
    let g := decoderGates positive b f tail i
    g.op.eval (g.inputs.map (value C x)) =
      decoded positive (value C x b) (fun j => value C x (tail j)) i := by
  rcases lt_trichotomy i.val (middle d) with before | eq | after
  · rw [decoded_lower positive _ _ _ before]
    simp [decoderGates,before,GateOp.eval]
  · rw [decoded_pivot positive _ _ _ eq]
    simp [decoderGates,eq,off,GateOp.eval]
  · have lower : ¬ i.val < middle d := by omega
    have other : i.val ≠ middle d := by omega
    rw [decoded_upper positive _ _ _ after]
    simp [decoderGates,lower,other,GateOp.eval]

def InversionResult {X : Type*} (input : X → List Bool) (n r : ℕ)
    (C : Circuit) {d : ℕ} (taps : Fin d → ℕ) :=
  {data : Circuit × (Fin d → ℕ) × ℕ × ℕ //
    let D := data.1
    let output := data.2.1
    let binary := data.2.2.1
    let inversions := data.2.2.2
    (C.gates <+: D.gates ∧ FanInTwo D ∧ ReadsBack n D) ∧
    (∀ i, output i < nextWire n D) ∧
    (binary ≤ 4*d ∧ inversions ≤ r) ∧
    (D.size = C.size + binary + inversions ∧ notCount D = notCount C + inversions) ∧
    ∀ x i, value D (input x) (output i) = !value C (input x) (taps i)}

namespace InversionResult

variable {X : Type*} {input : X → List Bool} {n r d : ℕ}
  {C : Circuit} {taps : Fin d → ℕ}

abbrev circuit (R : InversionResult input n r C taps) : Circuit := R.val.1

abbrev wires (R : InversionResult input n r C taps) : Fin d → ℕ := R.val.2.1

abbrev binary (R : InversionResult input n r C taps) : ℕ := R.val.2.2.1

abbrev inversions (R : InversionResult input n r C taps) : ℕ := R.val.2.2.2

theorem extension (R : InversionResult input n r C taps) : C.gates <+: R.circuit.gates :=
  R.property.1.1

theorem fanInTwo (R : InversionResult input n r C taps) : FanInTwo R.circuit :=
  R.property.1.2.1

theorem readsBack (R : InversionResult input n r C taps) : ReadsBack n R.circuit :=
  R.property.1.2.2

theorem valid (R : InversionResult input n r C taps) : ∀ i, R.wires i < nextWire n R.circuit :=
  R.property.2.1

theorem binaryBound (R : InversionResult input n r C taps) : R.binary ≤ 4*d :=
  R.property.2.2.1.1

theorem inversionsBound (R : InversionResult input n r C taps) : R.inversions ≤ r :=
  R.property.2.2.1.2

theorem size_eq (R : InversionResult input n r C taps) :
    R.circuit.size = C.size + R.binary + R.inversions := R.property.2.2.2.1.1

theorem count_eq (R : InversionResult input n r C taps) :
    notCount R.circuit = notCount C + R.inversions := R.property.2.2.2.1.2

theorem computes (R : InversionResult input n r C taps) :
    ∀ x i, value R.circuit (input x) (R.wires i) = !value C (input x) (taps i) :=
  R.property.2.2.2.2

end InversionResult

theorem InversionResult.nonnot_eq {X : Type*} {input : X → List Bool} {n r d : ℕ}
    {C : Circuit} {taps : Fin d → ℕ} (R : InversionResult input n r C taps) :
    R.circuit.size - notCount R.circuit = C.size - notCount C + R.binary := by
  have fits : notCount C ≤ C.size := List.length_filter_le _ _
  rw [R.size_eq,R.count_eq]
  omega

private theorem empty_inversion {X : Type*} (input : X → List Bool) {n r : ℕ}
    {C : Circuit} (fan : FanInTwo C) (back : ReadsBack n C) (taps : Fin 0 → ℕ) :
    Nonempty (InversionResult input n r C taps) := by
  exact ⟨⟨⟨C,taps,0,0⟩,⟨⟨List.prefix_rfl,fan,back⟩,fun i => Fin.elim0 i,
    ⟨by simp,by simp⟩,⟨rfl,rfl⟩,fun _ i => Fin.elim0 i⟩⟩⟩

set_option maxHeartbeats 2000000 in

theorem invert_taps {X : Type*} (input : X → List Bool) {n : ℕ}
    (length : ∀ x, (input x).length = n) {r d : ℕ} (bound : d < 2^r)
    {C : Circuit} (fan : FanInTwo C) (back : ReadsBack n C)
    (falseWire : ℕ) (falseLive : falseWire < nextWire n C)
    (falseValue : ∀ x, value C (input x) falseWire = false)
    (taps : Fin d → ℕ) (live : ∀ i, taps i < nextWire n C)
    (ordered : ∀ x, Antitone (fun i => value C (input x) (taps i))) :
    Nonempty (InversionResult input n r C taps) := by
  induction r generalizing d C with
  | zero =>
    have empty : d = 0 := by simpa using bound
    subst d
    exact empty_inversion input fan back taps
  | succ r ih =>
    by_cases positive : 0 < d
    · obtain ⟨F,pivotWire,foldWires,fExt,fFan,fBack,pivotValid,fValid,pivotValue,foldValue,fSize,fCount⟩ :=
        fold_taps input length positive fan back falseWire falseLive falseValue taps live
      have falseF := falseLive.trans_le (nextWire_le_of_prefix (n := n) fExt)
      have offF (x : X) : value F (input x) falseWire = false :=
        (old_value fExt (length x) falseLive).trans (falseValue x)
      have foldOrdered (x : X) : Antitone (fun i => value F (input x) (foldWires i)) := by
        rw [funext (foldValue x)]
        exact folded_antitone positive (ordered x)
      obtain ⟨R⟩ := ih (half_lt_pow bound) fFan fBack falseF offF foldWires fValid foldOrdered
      let gates := decoderGates positive pivotWire falseWire R.wires
      let D := appendFamily R.circuit gates
      let output (i : Fin d) := nextWire n R.circuit + i.val
      have step := appendFamily_prefix R.circuit gates
      have preserve := nextWire_le_of_prefix (n := n) R.extension
      have reads := decoder_reads positive (pivotValid.trans_le preserve)
        (falseF.trans_le preserve) R.valid
      have noNot : ∀ j, (gates j).op ≠ .not := by
        intro j
        change (decoderGates positive pivotWire falseWire R.wires j).op ≠ .not
        unfold decoderGates
        split
        · simp
        · split <;> simp
      have basis : FanInTwo D := appendFamily_fanInTwo (gate := gates) R.fanInTwo (by
        intro j
        change (decoderGates positive pivotWire falseWire R.wires j).op ∈
          ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧
          (decoderGates positive pivotWire falseWire R.wires j).inputs.length ≤ 2
        unfold decoderGates
        split
        · simp
        · split <;> simp)
      refine ⟨⟨⟨D,output,2*half d+R.binary+d,1+R.inversions⟩,
        ⟨⟨fExt.trans (R.extension.trans step),basis,appendFamily_readsBack R.readsBack reads⟩,
          ?_,⟨?_,?_⟩,⟨?_,?_⟩,?_⟩⟩⟩
      · intro i
        simpa only [D,output,appendFamily_nextWire,Nat.add_lt_add_iff_left] using i.isLt
      · change 2*half d + R.binary + d ≤ 4*d
        have rhs := R.binaryBound
        have halfBound : 2*half d ≤ d := by unfold half; omega
        omega
      · change 1 + R.inversions ≤ r + 1
        have rhs := R.inversionsBound
        omega
      · change D.size = C.size + (2*half d + R.binary + d) + (1 + R.inversions)
        rw [show D.size = R.circuit.size + d from appendFamily_size _ _, R.size_eq,fSize]
        omega
      · change notCount D = notCount C + (1 + R.inversions)
        rw [show notCount D = notCount R.circuit from appendFamily_notCount_eq noNot,R.count_eq,fCount]
        omega
      · intro x i
        have pivotOn : value R.circuit (input x) pivotWire =
            !value C (input x) (taps (pivot positive)) :=
          (old_value R.extension (length x) pivotValid).trans (pivotValue x)
        have off : value R.circuit (input x) falseWire = false :=
          (old_value R.extension (length x) falseF).trans (offF x)
        have tailOn (j : Fin (half d)) : value R.circuit (input x) (R.wires j) =
            !(folded positive (fun k => value C (input x) (taps k)) j) := by
          rw [R.computes,foldValue]
        have bits := family_value (gate := gates) reads (input x) (length x) i
        change value D (input x) (output i) = _ at bits
        rw [bits,decoder_value positive _ _ _ _ _ off,pivotOn]
        exact decoded_correct positive (ordered x) tailOn i
    · have empty : d = 0 := by omega
      subst d
      exact empty_inversion input fan back taps

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

private noncomputable def ceilingWire {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (complement : Fin d → ℕ) (u : Input n) : ℕ :=
  if below : rank P N d u < d then complement ⟨rank P N d u,below⟩ else n+1

private theorem ceilingWire_valid {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (C : Circuit) (complement : Fin d → ℕ) (u : Input n)
    (valid : ∀ i, complement i < nextWire (n+2) C) :
    ceilingWire P N complement u < nextWire (n+2) C := by
  unfold ceilingWire
  split
  · exact valid _
  · unfold nextWire
    omega

private theorem ceilingWire_value {n m d : ℕ} (P N : Input n → Fin m → Prop)
    (C : Circuit) (complement : Fin d → ℕ)
    (sem : ∀ (i : Fin d) (x : Input n), value C (withConstants x) (complement i) = true ↔
      ¬ i.val+1 ≤ rank P N d x) (u x : Input n) :
    value C (withConstants x) (ceilingWire P N complement u) = true ↔
      ¬ rank P N d u+1 ≤ rank P N d x := by
  unfold ceilingWire
  split
  · exact sem _ x
  · rename_i notBelow
    have atTop : rank P N d u = d := by
      have cap := rank_bound P N d u
      omega
    have noHigher : ¬ rank P N d u+1 ≤ rank P N d x := by
      rw [atTop]
      have cap := rank_bound P N d x
      omega
    exact ⟨fun _ => noHigher,fun _ => true_value C x⟩

set_option maxHeartbeats 1400000 in

theorem append_taps {n m d : ℕ} (P N : Input n → Fin m → Prop) (C : Circuit)
    (cone : Input n → ℕ) (complement : Fin d → ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (coneValid : ∀ u ∈ support P N, cone u < nextWire (n+2) C)
    (coneValue : ∀ u ∈ support P N, ∀ x : Input n, value C (withConstants x) (cone u) = true ↔ u ≤ x)
    (complementValid : ∀ i, complement i < nextWire (n+2) C)
    (complementValue : ∀ (i : Fin d) (x : Input n),
      value C (withConstants x) (complement i) = true ↔ ¬ i.val+1 ≤ rank P N d x)
    (bounded : ∀ x, ¬ Reach P N (d+1) x) :
    ∃ (D : Circuit) (tap : Fin m → Fin (n+2+D.size)),
      FanInTwo D ∧ ReadsBack (n+2) D ∧ D.output < n+2+D.size ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size ≤ C.size+(support P N).card+(positivePairs P).card ∧
      ∀ (x : Input n) (j : Fin m),
        (P x j → value D (withConstants x) (tap j).val = true) ∧
        (N x j → value D (withConstants x) (tap j).val = false) := by
  classical
  let words := (support P N).toList
  let gate (i : Fin words.length) : Gate := ⟨.and,[cone words[i],ceilingWire P N complement words[i]]⟩
  let guarded := appendFamily C gate
  let term (u : Input n) : ℕ := nextWire (n+2) C + words.idxOf u
  have gateReads (i : Fin words.length) (wire : ℕ) (used : wire ∈ (gate i).inputs) :
      wire < nextWire (n+2) C := by
    have present : words[i] ∈ support P N := Finset.mem_toList.mp (List.getElem_mem i.isLt)
    change wire ∈ [cone words[i],ceilingWire P N complement words[i]] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with rfl | rfl
    · exact coneValid _ present
    · exact ceilingWire_valid P N C complement _ complementValid
  have guardedBasis : FanInTwo guarded := by
    apply appendFamily_fanInTwo basis
    intro i
    change GateOp.and ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (2 : ℕ) ≤ 2
    simp
  have guardedReads : ReadsBack (n+2) guarded := appendFamily_readsBack (gate := gate) reads gateReads
  have guardedCost : guarded.size = C.size+(support P N).card := by simp [guarded,words]
  have guardedNot : notCount guarded = notCount C := by
    apply appendFamily_notCount_eq
    intro i
    simp [gate]
  have termValid (u : Input n) (present : u ∈ support P N) : term u < nextWire (n+2) guarded := by
    have found : words.idxOf u < words.length := List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr present)
    change nextWire (n+2) C + words.idxOf u < nextWire (n+2) (appendFamily C gate)
    rw [appendFamily_nextWire]
    exact Nat.add_lt_add_left found _
  have termValue (u : Input n) (present : u ∈ support P N) (x : Input n) :
      value guarded (withConstants x) (term u) = true ↔ guardedCone P N d u x := by
    let i : Fin words.length := ⟨words.idxOf u,List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr present)⟩
    have point : words[i] = u := List.getElem_idxOf i.isLt
    have evaluated := appendFamily_new (C := C) (gate := gate) (x := withConstants x)
      (by simpa only [withConstants_length] using gateReads) i
    rw [withConstants_length] at evaluated
    have equation : value guarded (withConstants x) (term u) =
      (value C (withConstants x) (cone words[i]) &&
        value C (withConstants x) (ceilingWire P N complement words[i])) := by
      simpa [guarded,term,i,gate,GateOp.eval] using evaluated
    rw [point] at equation
    change value guarded (withConstants x) (term u) = true ↔
      u ≤ x ∧ ¬ rank P N d u+1 ≤ rank P N d x
    rw [equation,Bool.and_eq_true,coneValue u present x,
      ceilingWire_value P N C complement complementValue u x]
  let rows (j : Fin m) : List ℕ := (positiveInputs P j).toList.map term
  have validRows : ∀ (j : Fin m) a, a ∈ rows j → a < nextWire (n+2) guarded := by
    intro j a member
    obtain ⟨u,present,rfl⟩ := List.mem_map.mp member
    exact termValid u (positive_input_support P N (Finset.mem_toList.mp present))
  obtain ⟨D,out,finalBasis,finalReads,finalPrefix,finalNot,finalSize,outValid,outValue⟩ :=
    append_or_rows guarded rows guardedBasis guardedReads validRows
  have rowCost : (∑ j : Fin m, (rows j).length) = (positivePairs P).card := by
    simpa [rows] using positive_incidence_count P
  have realized (x : Input n) (j : Fin m) :
      value D (withConstants x) (out j) = true ↔ tapAccepts P N d x j := by
    rw [outValue]
    constructor
    · rintro ⟨a,member,active⟩
      obtain ⟨u,present,rfl⟩ := List.mem_map.mp member
      have positive := Finset.mem_toList.mp present
      exact ⟨u,positive,(termValue u (positive_input_support P N positive) x).mp active⟩
    · rintro ⟨u,positive,active⟩
      exact ⟨term u,List.mem_map.mpr ⟨u,Finset.mem_toList.mpr positive,rfl⟩,
        (termValue u (positive_input_support P N positive) x).mpr active⟩
  let taps (j : Fin m) : Fin (n+2+(withOutput D 0).size) := ⟨out j,outValid j⟩
  refine ⟨withOutput D 0,taps,finalBasis,finalReads,?_,
    (appendFamily_prefix C gate).trans finalPrefix,finalNot.trans guardedNot,?_,?_⟩
  · simp only [withOutput_output,withOutput_size]
    omega
  · rw [withOutput_size,finalSize,guardedCost,rowCost]
  · intro x j
    change (P x j → value D (withConstants x) (out j) = true) ∧
      (N x j → value D (withConstants x) (out j) = false)
    refine ⟨fun positive => (realized x j).mpr (tap_accepts_positive P N d positive),?_⟩
    intro negative
    exact Bool.eq_false_iff.mpr fun active =>
      tap_rejects_negative P N bounded negative ((realized x j).mp active)

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

def Fits {n m : ℕ} (P N : Input n → Fin m → Prop) (r : ℕ) (cost : ℕ → Prop) : Prop :=
  ∃ (C : Circuit) (tap : Fin m → Fin (n+2+C.size)),
    FanInTwo C ∧ ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧ notCount C ≤ r ∧
    cost (C.size-notCount C) ∧ ∀ (x : Input n) (j : Fin m),
      (P x j → value C (withConstants x) (tap j).val = true) ∧
      (N x j → value C (withConstants x) (tap j).val = false)

theorem upper_fits {n m r d : ℕ} (P N : Input n → Fin m → Prop)
    (bound : d < 2^r) (bounded : ∀ x, ¬ Reach P N (d+1) x) :
    Fits P N r (fun b => b ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d) := by
  obtain ⟨A,cone,aBasis,aReads,aSize,aNot,aSem,_⟩ := supportConeTable_empty P N
  obtain ⟨B,thresholds,bBasis,bReads,bExtends,bNot,bSize,bLive,bSem⟩ :=
    append_thresholds P N d A cone aBasis aReads
      (fun u hu => (aSem u hu).1) (fun u hu => (aSem u hu).2)
  have falseLive : n < nextWire (n+2) B := by unfold nextWire; omega
  obtain ⟨I⟩ := invert_taps (withConstants (n := n)) withConstants_length bound
    bBasis bReads n falseLive (false_value B) thresholds bLive (threshold_antitone bSem)
  have extension : A.gates <+: I.circuit.gates := bExtends.trans I.extension
  have coneLive (u : Input n) (hu : u ∈ support P N) :
      cone u < nextWire (n+2) I.circuit :=
    (aSem u hu).1.trans_le (nextWire_le_of_prefix extension)
  have coneValue (u : Input n) (hu : u ∈ support P N) (x : Input n) :
      value I.circuit (withConstants x) (cone u) = true ↔ u ≤ x := by
    have live : cone u < nextWire (withConstants x).length A := by
      rw [withConstants_length]
      exact (aSem u hu).1
    rw [value_of_prefix extension live]
    exact (aSem u hu).2 x
  have complementValue (i : Fin d) (x : Input n) :
      value I.circuit (withConstants x) (I.wires i) = true ↔ ¬ i.val+1 ≤ rank P N d x := by
    rw [I.computes, ← bSem x i]
    cases value B (withConstants x) (thresholds i) <;> decide
  obtain ⟨C,tap,cBasis,cReads,cOut,_,cNot,cSize,labels⟩ :=
    append_taps P N I.circuit cone I.wires I.fanInTwo I.readsBack
      coneLive coneValue I.valid complementValue bounded
  have bZero : notCount B = 0 := bNot.trans aNot
  have cInversions : notCount C = I.inversions := by
    rw [cNot,I.count_eq,bZero,Nat.zero_add]
  have cBinary : C.size-notCount C ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d := by
    have inversionSize := I.size_eq
    have binaryBudget := I.binaryBound
    rw [cInversions,Nat.add_mul]
    omega
  exact ⟨C,tap,cBasis,cReads,cOut,cInversions.le.trans I.inversionsBound,cBinary,labels⟩

theorem solve_fall_1228 (n m r : ℕ) (P N : Input n → Fin m → Prop) :
    (Fits P N r (fun _ => True) ↔ ∀ x, ¬ Reach P N (2^r) x) ∧
    ∀ d : ℕ, d < 2^r → (∀ x, ¬ Reach P N (d+1) x) →
      Fits P N r (fun b => b ≤ (n+2)*(support P N).card+(positivePairs P).card+5*d) := by
  constructor
  · constructor
    · rintro ⟨C,tap,basis,_,_,budget,_,labels⟩
      exact no_packing_of_taps (fun j => (tap j).val) basis budget labels
    · intro bounded
      have positive : 0 < (2:ℕ)^r := Nat.pow_pos (by decide)
      have below : (2:ℕ)^r-1 < 2^r := by omega
      have successor : (2:ℕ)^r-1+1 = 2^r := by omega
      have bounded' : ∀ x, ¬ Reach P N ((2:ℕ)^r-1+1) x := by simpa only [successor] using bounded
      obtain ⟨C,tap,basis,reads,output,budget,_,labels⟩ := upper_fits P N below bounded'
      exact ⟨C,tap,basis,reads,output,budget,True.intro,labels⟩
  · intro d bound bounded
    exact upper_fits P N bound bounded

theorem crit1228 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m r : Nat) (P N : (Fin n → Bool) → Fin m → Prop),
  let X := Fin n → Bool
  let reach := Nat.rec (motive := fun _ => X → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j)
  let S := (Finset.univ.filter (fun x : X => ∃ j, P x j ∨ N x j)).card
  let L := (Finset.univ.filter (fun z : X × Fin m => P z.1 z.2)).card
  let fits := fun (cost : Nat → Prop) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (n+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      cost (C.size-PEqualNP.NotBracket.notCount C) ∧ ∀ (x : X) (j : Fin m),
        let w := (C.wires (List.ofFn x ++ [false,true])).getD (tap j).val false
        (P x j → w=true) ∧ (N x j → w=false)
  (fits (fun _ => True) ↔ ∀ x, ¬ reach (2^r) x) ∧
    ∀ d : Nat, d < 2^r → (∀ x, ¬ reach (d+1) x) →
      fits (fun b => b ≤ (n+2)*S + L + 5*d)) := by
  intro n m r P N
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  have support_eq : (Finset.univ.filter (fun x : Fin n → Bool => ∃ j, P x j ∨ N x j)) =
      Base.support P N := by
    ext x
    simp [Base.mem_support]
  have pairs_eq : (Finset.univ.filter (fun z : (Fin n → Bool) × Fin m => P z.1 z.2)) =
      Base.positivePairs P := by
    ext z
    simp [Base.mem_positivePairs]
  dsimp only
  rw [support_eq, pairs_eq]
  exact Base.solve_fall_1228 n m r P N

end Base

namespace Base

def R94 {d t : Nat} (P N : (Fin d → Bool) → Fin t → Prop) : Nat → (Fin d → Bool) → Prop :=
  Nat.rec (motive := fun _ => (Fin d → Bool) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j)

theorem r94_succ {d t : Nat} (P N : (Fin d → Bool) → Fin t → Prop) (k : Nat) (x : Fin d → Bool) :
    R94 P N (k+1) x ↔ ∃ u v j, R94 P N k u ∧ u ≤ v ∧ v ≤ x ∧ P u j ∧ N v j := Iff.rfl

theorem r94_zero {d t : Nat} (P N : (Fin d → Bool) → Fin t → Prop) (x : Fin d → Bool) :
    R94 P N 0 x := trivial

theorem r94_mono {d t : Nat} (P N : (Fin d → Bool) → Fin t → Prop) :
    ∀ k (x y : Fin d → Bool), R94 P N k x → x ≤ y → R94 P N k y
  | 0, _, y, _, _ => r94_zero P N y
  | k+1, x, y, h, hxy => by
    obtain ⟨u, v, j, h1, h2, h3, h4, h5⟩ := (r94_succ P N k x).1 h
    exact (r94_succ P N k y).2 ⟨u, v, j, h1, h2, le_trans h3 hxy, h4, h5⟩

theorem chain_reach {A : Type} {d t : Nat} (xs : A → Fin d → Bool) (ys : A → Fin t → Bool) (K : Nat)
    (a b : Fin K → A)
    (h1 : ∀ i, xs (a i) ≤ xs (b i) ∧ ∃ j, ys (a i) j=true ∧ ys (b i) j=false)
    (h2 : ∀ i j : Fin K, i.val+1=j.val → xs (b i) ≤ xs (a j)) :
    ∀ k (hk : k < K), R94 (fun u j => ∃ i, xs i = u ∧ ys i j = true)
      (fun u j => ∃ i, xs i = u ∧ ys i j = false) (k+1) (xs (b ⟨k,hk⟩))
  | 0, hk => by
    obtain ⟨hle, j, hj1, hj2⟩ := h1 ⟨0,hk⟩
    exact (r94_succ _ _ 0 _).2 ⟨xs (a ⟨0,hk⟩), xs (b ⟨0,hk⟩), j, r94_zero _ _ _, hle, le_refl _,
      ⟨_, rfl, hj1⟩, ⟨_, rfl, hj2⟩⟩
  | k+1, hk => by
    have ih := chain_reach xs ys K a b h1 h2 k (by omega)
    obtain ⟨hle, j, hj1, hj2⟩ := h1 ⟨k+1,hk⟩
    exact (r94_succ _ _ (k+1) _).2 ⟨xs (a ⟨k+1,hk⟩), xs (b ⟨k+1,hk⟩), j,
      r94_mono _ _ _ _ _ ih (h2 ⟨k, by omega⟩ ⟨k+1,hk⟩ rfl), hle, le_refl _,
      ⟨_, rfl, hj1⟩, ⟨_, rfl, hj2⟩⟩

theorem reach_chain {A : Type} {d t : Nat} (xs : A → Fin d → Bool) (ys : A → Fin t → Bool) :
    ∀ k x, R94 (fun u j => ∃ i, xs i = u ∧ ys i j = true)
      (fun u j => ∃ i, xs i = u ∧ ys i j = false) k x →
    ∃ a b : Fin k → A, (∀ i, xs (a i) ≤ xs (b i) ∧ ∃ j, ys (a i) j=true ∧ ys (b i) j=false) ∧
      (∀ i j : Fin k, i.val+1=j.val → xs (b i) ≤ xs (a j)) ∧ ∀ i, xs (b i) ≤ x
  | 0, x, _ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | k+1, x, h => by
    obtain ⟨u, v, j, hr, huv, hvx, ⟨i1, hi1, hj1⟩, ⟨i2, hi2, hj2⟩⟩ := (r94_succ _ _ k x).1 h
    obtain ⟨a, b, ha, hab, hb⟩ := reach_chain xs ys k u hr
    subst hi1; subst hi2
    refine ⟨fun i => if hi : i.val < k then a ⟨i, hi⟩ else i1,
      fun i => if hi : i.val < k then b ⟨i, hi⟩ else i2, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i.val < k
      · simp only [dif_pos hi]; exact ha _
      · simp only [dif_neg hi]; exact ⟨huv, j, hj1, hj2⟩
    · intro i i' hii'
      have := i'.isLt
      have hi : i.val < k := by omega
      by_cases hi' : i'.val < k
      · simp only [dif_pos hi, dif_pos hi']; exact hab _ _ hii'
      · simp only [dif_pos hi, dif_neg hi']; exact hb _
    · intro i
      by_cases hi : i.val < k
      · simp only [dif_pos hi]; exact le_trans (hb _) (le_trans huv hvx)
      · simp only [dif_neg hi]; exact hvx

theorem fits_iff {A : Type} {d t : Nat} (xs : A → Fin d → Bool) (ys : A → Fin t → Bool) (r : Nat) :
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin t → Fin (d+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
      C.output < d+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ i j, (C.wires (List.ofFn (xs i) ++ [false,true])).getD (p j).val false=ys i j) ↔
    ¬ ∃ a b : Fin (2^r) → A, (∀ i, xs (a i) ≤ xs (b i) ∧
      ∃ j, ys (a i) j=true ∧ ys (b i) j=false) ∧
      ∀ i j : Fin (2^r), i.val+1=j.val → xs (b i) ≤ xs (a j) := by
  have H := (crit1228 d t r (fun u j => ∃ i, xs i = u ∧ ys i j = true)
      (fun u j => ∃ i, xs i = u ∧ ys i j = false)).1
  constructor
  · intro hf hp
    obtain ⟨C, p, h1, h2, h3, h4, h5⟩ := hf
    have hn := H.1 ⟨C, p, h1, h2, h3, h4, trivial, fun x j =>
      ⟨fun ⟨i, hi, hj⟩ => by subst hi; rw [h5, hj], fun ⟨i, hi, hj⟩ => by subst hi; rw [h5, hj]⟩⟩
    obtain ⟨a, b, ha, hab⟩ := hp
    have hpos : 0 < 2^r := Nat.two_pow_pos r
    have hh := chain_reach xs ys _ a b ha hab (2^r-1) (by omega)
    have e : 2^r-1+1 = 2^r := by omega
    rw [e] at hh
    exact hn _ hh
  · intro hnp
    have hnr : ∀ x, ¬ R94 (fun u j => ∃ i, xs i = u ∧ ys i j = true)
        (fun u j => ∃ i, xs i = u ∧ ys i j = false) (2^r) x := by
      intro x hx
      obtain ⟨a, b, ha, hab, -⟩ := reach_chain xs ys _ x hx
      exact hnp ⟨a, b, ha, hab⟩
    obtain ⟨C, p, h1, h2, h3, h4, -, h5⟩ := H.2 hnr
    refine ⟨C, p, h1, h2, h3, h4, fun i j => ?_⟩
    cases hy : ys i j
    · exact (h5 (xs i) j).2 ⟨i, rfl, hy⟩
    · exact (h5 (xs i) j).1 ⟨i, rfl, hy⟩

theorem ble {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  revert h ha; cases a <;> cases b <;> decide
theorem ble2 {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  revert h; cases a <;> cases b <;> decide

end Base

namespace Lib1431Partial
open Base

theorem chain_reach_partial {A : Type} {d t : Nat} (xs : A → Fin d → Bool) (P N : A → Fin t → Prop) (K : Nat)
    (a b : Fin K → A)
    (h1 : ∀ i, xs (a i) ≤ xs (b i) ∧ ∃ j, P (a i) j ∧ N (b i) j)
    (h2 : ∀ i j : Fin K, i.val+1=j.val → xs (b i) ≤ xs (a j)) :
    ∀ k (hk : k < K), R94 (fun u j => ∃ i, xs i = u ∧ P i j)
      (fun u j => ∃ i, xs i = u ∧ N i j) (k+1) (xs (b ⟨k,hk⟩))
  | 0, hk => by
    obtain ⟨hle, j, hj1, hj2⟩ := h1 ⟨0,hk⟩
    exact (r94_succ _ _ 0 _).2 ⟨xs (a ⟨0,hk⟩), xs (b ⟨0,hk⟩), j, r94_zero _ _ _, hle, le_refl _,
      ⟨_, rfl, hj1⟩, ⟨_, rfl, hj2⟩⟩
  | k+1, hk => by
    have ih := chain_reach_partial xs P N K a b h1 h2 k (by omega)
    obtain ⟨hle, j, hj1, hj2⟩ := h1 ⟨k+1,hk⟩
    exact (r94_succ _ _ (k+1) _).2 ⟨xs (a ⟨k+1,hk⟩), xs (b ⟨k+1,hk⟩), j,
      r94_mono _ _ _ _ _ ih (h2 ⟨k, by omega⟩ ⟨k+1,hk⟩ rfl), hle, le_refl _,
      ⟨_, rfl, hj1⟩, ⟨_, rfl, hj2⟩⟩

theorem reach_chain_partial {A : Type} {d t : Nat} (xs : A → Fin d → Bool) (P N : A → Fin t → Prop) :
    ∀ k x, R94 (fun u j => ∃ i, xs i = u ∧ P i j)
      (fun u j => ∃ i, xs i = u ∧ N i j) k x →
    ∃ a b : Fin k → A, (∀ i, xs (a i) ≤ xs (b i) ∧ ∃ j, P (a i) j ∧ N (b i) j) ∧
      (∀ i j : Fin k, i.val+1=j.val → xs (b i) ≤ xs (a j)) ∧ ∀ i, xs (b i) ≤ x
  | 0, x, _ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | k+1, x, h => by
    obtain ⟨u, v, j, hr, huv, hvx, ⟨i1, hi1, hj1⟩, ⟨i2, hi2, hj2⟩⟩ := (r94_succ _ _ k x).1 h
    obtain ⟨a, b, ha, hab, hb⟩ := reach_chain_partial xs P N k u hr
    subst hi1; subst hi2
    refine ⟨fun i => if hi : i.val < k then a ⟨i, hi⟩ else i1,
      fun i => if hi : i.val < k then b ⟨i, hi⟩ else i2, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i.val < k
      · simp only [dif_pos hi]; exact ha _
      · simp only [dif_neg hi]; exact ⟨huv, j, hj1, hj2⟩
    · intro i i' hii'
      have := i'.isLt
      have hi : i.val < k := by omega
      by_cases hi' : i'.val < k
      · simp only [dif_pos hi, dif_pos hi']; exact hab _ _ hii'
      · simp only [dif_pos hi, dif_neg hi']; exact hb _
    · intro i
      by_cases hi : i.val < k
      · simp only [dif_pos hi]; exact le_trans (hb _) (le_trans huv hvx)
      · simp only [dif_neg hi]; exact hvx

theorem fits_iff {A : Type} {d t : Nat} (xs : A → Fin d → Bool)
    (P N : A → Fin t → Prop) (r : Nat) :
    (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin t → Fin (d+2+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
      C.output < d+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
      ∀ i j, (P i j → (C.wires (List.ofFn (xs i) ++ [false,true])).getD (p j).val false=true) ∧
        (N i j → (C.wires (List.ofFn (xs i) ++ [false,true])).getD (p j).val false=false)) ↔
    ¬ ∃ a b : Fin (2^r) → A, (∀ i, xs (a i) ≤ xs (b i) ∧
      ∃ j, P (a i) j ∧ N (b i) j) ∧
      ∀ i j : Fin (2^r), i.val+1=j.val → xs (b i) ≤ xs (a j) := by
  have H := (crit1228 d t r (fun u j => ∃ i, xs i = u ∧ P i j)
      (fun u j => ∃ i, xs i = u ∧ N i j)).1
  constructor
  · intro hf hp
    obtain ⟨C,p,h1,h2,h3,h4,h5⟩ := hf
    have hn := H.1 ⟨C,p,h1,h2,h3,h4,trivial,fun x j =>
      ⟨fun ⟨i,hi,hp⟩ => by subst hi; exact (h5 i j).1 hp,
       fun ⟨i,hi,hn⟩ => by subst hi; exact (h5 i j).2 hn⟩⟩
    obtain ⟨a,b,ha,hab⟩ := hp
    have hpos : 0 < 2^r := Nat.two_pow_pos r
    have hh := chain_reach_partial xs P N _ a b ha hab (2^r-1) (by omega)
    have e : 2^r-1+1=2^r := by omega
    rw [e] at hh
    exact hn _ hh
  · intro hnp
    have hnr : ∀ x, ¬ R94 (fun u j=>∃ i,xs i=u ∧ P i j)
        (fun u j=>∃ i,xs i=u ∧ N i j) (2^r) x := by
      intro x hx
      obtain ⟨a,b,ha,hab,-⟩ := reach_chain_partial xs P N _ x hx
      exact hnp ⟨a,b,ha,hab⟩
    obtain ⟨C,p,h1,h2,h3,h4,-,h5⟩ := H.2 hnr
    exact ⟨C,p,h1,h2,h3,h4,fun i j=>
      ⟨fun hp=>(h5 (xs i) j).1 ⟨i,rfl,hp⟩,
       fun hn=>(h5 (xs i) j).2 ⟨i,rfl,hn⟩⟩⟩

end Lib1431Partial


namespace Lib1436Subset

def shade (n : Nat) : Bool := decide (n % 2=0)

theorem shade_succ (n : Nat) : shade (n+1)= !shade n := by
  unfold shade
  have hm := Nat.mod_lt n (show 0 < 2 by decide)
  by_cases hn : n % 2=0
  · have hs : (n+1) % 2≠0 := by omega
    simp [hn,hs]
  · have hs : (n+1) % 2=0 := by omega
    simp [hn,hs]

variable {α : Type*} [DecidableEq α]

inductive Path (E : Bool → α → Prop) (R : α → α → Prop) : Nat → Finset α → Prop
  | nil : Path E R 0 ∅
  | step {n : Nat} {S : Finset α} (j : α) (previous : Path E R n S)
      (enabled : E (shade n) j) (incoming : ∀i∈insert j S,R i j) :
      Path E R (n+1) (insert j S)

inductive DP (E : Bool → α → Prop) (R : α → α → Prop) : Finset α → Prop
  | nil : DP E R ∅
  | step {S : Finset α} (j : α) (previous : DP E R S) (fresh : j∉S)
      (enabled : E (shade S.card) j) (incoming : ∀i∈insert j S,R i j) : DP E R (insert j S)

def Collision (E : Bool → α → Prop) (R : α → α → Prop) : Prop :=
  ∃i j b,E b i ∧ E (!b) j ∧ R i i ∧ R i j ∧ R j i ∧ R j j

theorem step_fresh {E : Bool → α → Prop} {R : α → α → Prop}
    (hnoc : ¬Collision E R) {n : Nat} {S : Finset α} (j : α)
    (hp : Path E R n S) (he : E (shade n) j) (hr : ∀i∈insert j S,R i j) : j∉S := by
  intro hj
  cases hp with
  | nil => exact Finset.notMem_empty j hj
  | @step n S i hp hi hri =>
    have hiS : i∈insert i S := Finset.mem_insert_self _ _
    have hji : R j i := hri j hj
    have hij : R i j := hr i (Finset.mem_insert_of_mem hiS)
    have hjj : R j j := hr j (Finset.mem_insert_self _ _)
    have he' : E (!shade n) j := by simpa only [shade_succ] using he
    exact hnoc ⟨i,j,shade n,hi,he',hri i hiS,hij,hji,hjj⟩

theorem path_card {E : Bool → α → Prop} {R : α → α → Prop}
    (hnoc : ¬Collision E R) {n : Nat} {S : Finset α} (hp : Path E R n S) : S.card=n := by
  induction hp with
  | nil => rfl
  | @step n S j hp he hr ih =>
    rw [Finset.card_insert_of_notMem (step_fresh hnoc j hp he hr),ih]

theorem path_bound [Fintype α] {E : Bool → α → Prop} {R : α → α → Prop}
    (hnoc : ¬Collision E R) {n : Nat} {S : Finset α} (hp : Path E R n S) : n ≤ Fintype.card α := by
  rw [←path_card hnoc hp]
  exact Finset.card_le_univ S

theorem path_of_dp {E : Bool → α → Prop} {R : α → α → Prop}
    {S : Finset α} (hp : DP E R S) : Path E R S.card S := by
  induction hp with
  | nil => exact Path.nil
  | @step S j hp hj he hr ih =>
    simpa only [Finset.card_insert_of_notMem hj] using Path.step j ih he hr

theorem dp_of_path {E : Bool → α → Prop} {R : α → α → Prop}
    (hnoc : ¬Collision E R) {n : Nat} {S : Finset α} (hp : Path E R n S) : DP E R S := by
  induction hp with
  | nil => exact DP.nil
  | @step n S j hp he hr ih =>
    exact DP.step j ih (step_fresh hnoc j hp he hr)
      (by simpa only [path_card hnoc hp] using he) hr

theorem dp_iff_path {E : Bool → α → Prop} {R : α → α → Prop}
    (hnoc : ¬Collision E R) (S : Finset α) : DP E R S ↔ ∃n,Path E R n S :=
  ⟨fun h=>⟨S.card,path_of_dp h⟩,fun ⟨_,h⟩=>dp_of_path hnoc h⟩

theorem dp_recurrence (E : Bool → α → Prop) (R : α → α → Prop) (S : Finset α) :
    DP E R S ↔ S=∅ ∨ ∃j∈S,DP E R (S.erase j) ∧
      E (shade (S.card-1)) j ∧ ∀i∈S,R i j := by
  constructor
  · intro hp
    cases hp with
    | nil => exact Or.inl rfl
    | @step S j hp hj he hr =>
      right
      refine ⟨j,Finset.mem_insert_self _ _,?_,?_,hr⟩
      · rw [Finset.erase_insert hj]
        exact hp
      · simpa only [Finset.card_insert_of_notMem hj,Nat.add_sub_cancel] using he
  · rintro (rfl | ⟨j,hj,hp,he,hr⟩)
    · exact DP.nil
    · have H := DP.step j hp (Finset.notMem_erase j S)
        (by simpa only [Finset.card_erase_of_mem hj] using he)
        (by simpa only [Finset.insert_erase hj] using hr)
      simpa only [Finset.insert_erase hj] using H

end Lib1436Subset


namespace Lib1436Boxes
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def Box (lo hi : α → Finset β) (i : α) (X : Finset β) : Prop := lo i⊆X ∧ X⊆hi i

theorem intersection_iff (lo hi : α → Finset β) (i j : α) :
    (∃X,Box lo hi i X ∧ Box lo hi j X) ↔
      lo i⊆hi i ∧ lo i⊆hi j ∧ lo j⊆hi i ∧ lo j⊆hi j := by
  constructor
  · rintro ⟨X,⟨hli,hui⟩,⟨hlj,huj⟩⟩
    exact ⟨hli.trans hui,hli.trans huj,hlj.trans hui,hlj.trans huj⟩
  · rintro ⟨hii,hij,hji,hjj⟩
    refine ⟨lo i∪lo j,⟨Finset.subset_union_left,?_⟩,⟨Finset.subset_union_right,?_⟩⟩
    · exact Finset.union_subset hii hji
    · exact Finset.union_subset hij hjj

def Bad (E : Bool → α → Prop) (lo hi : α → Finset β) : Prop :=
  ∃i j X,E true i ∧ E false j ∧ Box lo hi i X ∧ Box lo hi j X

theorem collision_iff_bad (E : Bool → α → Prop) (lo hi : α → Finset β) :
    Lib1436Subset.Collision E (fun i j=>lo i⊆hi j) ↔ Bad E lo hi := by
  constructor
  · rintro ⟨i,j,b,hei,hej,hii,hij,hji,hjj⟩
    obtain ⟨X,hXi,hXj⟩ := (intersection_iff lo hi i j).mpr ⟨hii,hij,hji,hjj⟩
    cases b with
    | false => exact ⟨j,i,X,hej,hei,hXj,hXi⟩
    | true => exact ⟨i,j,X,hei,hej,hXi,hXj⟩
  · rintro ⟨i,j,X,hei,hej,hXi,hXj⟩
    obtain ⟨hii,hij,hji,hjj⟩ := (intersection_iff lo hi i j).mp ⟨X,hXi,hXj⟩
    exact ⟨i,j,true,hei,hej,hii,hij,hji,hjj⟩

noncomputable def prefixUnion {n : Nat} (lo : α → Finset β) (lab : Fin n → α) (i : Fin n) : Finset β := by
  classical
  exact (Finset.univ.filter (fun j=>j ≤ i)).biUnion (fun j=>lo (lab j))

theorem prefixUnion_monotone {n : Nat} (lo : α → Finset β) (lab : Fin n → α) :
    Monotone (prefixUnion lo lab) := by
  classical
  intro i j hij x hx
  obtain ⟨l,hl,hx⟩ := Finset.mem_biUnion.mp hx
  have hli := (Finset.mem_filter.mp hl).2
  exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hli.trans hij⟩,hx⟩

theorem prefixUnion_box {n : Nat} (lo hi : α → Finset β) (lab : Fin n → α)
    (hR : ∀i j,i ≤ j → lo (lab i)⊆hi (lab j)) (i : Fin n) :
    Box lo hi (lab i) (prefixUnion lo lab i) := by
  classical
  constructor
  · intro x hx
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_refl _⟩,hx⟩
  · intro x hx
    obtain ⟨j,hj,hx⟩ := Finset.mem_biUnion.mp hx
    exact hR j i (Finset.mem_filter.mp hj).2 hx

theorem ordered_iff_realizable {n : Nat} (lo hi : α → Finset β) (lab : Fin n → α) :
    (∀i j,i ≤ j → lo (lab i)⊆hi (lab j)) ↔
      ∃X : Fin n → Finset β,Monotone X ∧ ∀i,Box lo hi (lab i) (X i) := by
  constructor
  · intro hR
    exact ⟨prefixUnion lo lab,prefixUnion_monotone lo lab,prefixUnion_box lo hi lab hR⟩
  · rintro ⟨X,hmono,hbox⟩ i j hij
    exact (hbox i).1.trans ((hmono hij).trans (hbox j).2)

end Lib1436Boxes

namespace Lib1436Subset
variable {α : Type*} [DecidableEq α]

theorem image_split {n : Nat} (lab : Fin (n+1) → α) :
    Finset.univ.image lab = insert (lab (Fin.last n)) (Finset.univ.image (fun i : Fin n=>lab i.castSucc)) := by
  classical
  ext a
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.lastCases ?_ (fun i=>?_) i
    · exact Or.inl rfl
    · exact Or.inr ⟨i,rfl⟩
  · rintro (rfl | ⟨i,rfl⟩)
    · exact ⟨Fin.last n,rfl⟩
    · exact ⟨i.castSucc,rfl⟩

def Ordered (E : Bool → α → Prop) (R : α → α → Prop) (n : Nat) (S : Finset α) : Prop :=
  ∃lab : Fin n → α,Finset.univ.image lab=S ∧
    (∀i,E (shade i.val) (lab i)) ∧ ∀i j,i ≤ j → R (lab i) (lab j)

theorem ordered_of_path {E : Bool → α → Prop} {R : α → α → Prop}
    {n : Nat} {S : Finset α} (hp : Path E R n S) : Ordered E R n S := by
  classical
  induction hp with
  | nil =>
    exact ⟨Fin.elim0,by simp,fun i=>i.elim0,fun i=>i.elim0⟩
  | @step n S a hp hea hra ih =>
    obtain ⟨lab,him,he,hr⟩ := ih
    let lab' : Fin (n+1) → α := Fin.lastCases a lab
    refine ⟨lab',?_,?_,?_⟩
    · rw [image_split]
      simpa only [lab',Fin.lastCases_last,Fin.lastCases_castSucc,him]
    · intro i
      refine Fin.lastCases ?_ (fun i=>?_) i
      · simpa only [lab',Fin.lastCases_last,Fin.val_last] using hea
      · simpa only [lab',Fin.lastCases_castSucc,Fin.val_castSucc] using he i
    · intro i j
      refine Fin.lastCases ?_ (fun j=>?_) j
      · intro hij
        refine Fin.lastCases ?_ (fun i=>?_) i
        · simpa only [lab',Fin.lastCases_last] using hra a (Finset.mem_insert_self _ _)
        · simp only [lab',Fin.lastCases_castSucc,Fin.lastCases_last]
          apply hra (lab i)
          apply Finset.mem_insert_of_mem
          rw [←him]
          exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      · refine Fin.lastCases ?_ (fun i=>?_) i
        · intro hij
          have hj := j.isLt
          have hh : n ≤ j.val := hij
          omega
        · intro hij
          simpa only [lab',Fin.lastCases_castSucc] using hr i j hij

theorem path_of_ordered {E : Bool → α → Prop} {R : α → α → Prop}
    {n : Nat} (lab : Fin n → α) (he : ∀i,E (shade i.val) (lab i))
    (hr : ∀i j,i ≤ j → R (lab i) (lab j)) : Path E R n (Finset.univ.image lab) := by
  classical
  induction n with
  | zero => simpa using (Path.nil (E:=E) (R:=R))
  | succ n ih =>
    let old : Fin n → α := fun i=>lab i.castSucc
    have ho : Path E R n (Finset.univ.image old) :=
      ih old (fun i=>he i.castSucc) (fun i j hij=>hr i.castSucc j.castSucc hij)
    have hin : ∀i∈insert (lab (Fin.last n)) (Finset.univ.image old),R i (lab (Fin.last n)) := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hr _ _ (le_refl _)
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
        exact hr j.castSucc (Fin.last n) (Fin.le_last _)
    have H := Path.step (lab (Fin.last n)) ho (he (Fin.last n)) hin
    rw [image_split]
    exact H

theorem path_iff_ordered {E : Bool → α → Prop} {R : α → α → Prop}
    {n : Nat} {S : Finset α} : Path E R n S ↔ Ordered E R n S := by
  constructor
  · exact ordered_of_path
  · rintro ⟨lab,rfl,he,hr⟩
    exact path_of_ordered lab he hr

theorem path_prefix {E : Bool → α → Prop} {R : α → α → Prop}
    {n q : Nat} {S : Finset α} (hp : Path E R n S) (hq : q ≤ n) :
    ∃T⊆S,Path E R q T := by
  classical
  obtain ⟨lab,him,he,hr⟩ := ordered_of_path hp
  let emb (i : Fin q) : Fin n := ⟨i.val,lt_of_lt_of_le i.isLt hq⟩
  let sub : Fin q → α := fun i=>lab (emb i)
  refine ⟨Finset.univ.image sub,?_,path_of_ordered sub (fun i=>he (emb i)) (fun i j hij=>hr (emb i) (emb j) hij)⟩
  intro x hx
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  rw [←him]
  exact Finset.mem_image.mpr ⟨emb i,Finset.mem_univ _,rfl⟩

end Lib1436Subset

namespace Lib1436Pairs

def index {K : Nat} (i : Fin (2*K)) : Fin K := ⟨i.val/2,by have := i.isLt;omega⟩

def weave {K : Nat} {γ : Type*} (a b : Fin K → γ) (i : Fin (2*K)) : γ :=
  if i.val % 2=0 then a (index i) else b (index i)

def even {K : Nat} (i : Fin K) : Fin (2*K) := ⟨2*i.val,by have := i.isLt;omega⟩
def odd {K : Nat} (i : Fin K) : Fin (2*K) := ⟨2*i.val+1,by have := i.isLt;omega⟩

theorem index_even {K : Nat} (i : Fin K) : index (even i)=i := by
  apply Fin.ext
  simp [index,even,Nat.mul_comm]

theorem index_odd {K : Nat} (i : Fin K) : index (odd i)=i := by
  apply Fin.ext
  dsimp [index,odd]
  omega

theorem weave_even {K : Nat} {γ : Type*} (a b : Fin K → γ) (i : Fin K) : weave a b (even i)=a i := by
  have hp : (even i).val % 2=0 := by dsimp [even];omega
  simp only [weave,if_pos hp,index_even]

theorem weave_odd {K : Nat} {γ : Type*} (a b : Fin K → γ) (i : Fin K) : weave a b (odd i)=b i := by
  have hp : ¬(odd i).val % 2=0 := by dsimp [odd];omega
  simp only [weave,if_neg hp,index_odd]

theorem weave_monotone {K : Nat} {γ : Type*} [Preorder γ] (a b : Fin K → γ)
    (hab : ∀i,a i ≤ b i) (hnext : ∀i j,i.val+1=j.val → b i ≤ a j) : Monotone (weave a b) := by
  cases K with
  | zero => intro i; exact i.elim0
  | succ K =>
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    by_cases hp : i.val % 2=0
    · have hp' : ¬(i.val+1)%2=0 := by omega
      have he : index (K:=K+1) i.succ=index (K:=K+1) i.castSucc := by apply Fin.ext;dsimp [index];omega
      simp only [weave,Fin.val_castSucc,Fin.val_succ,if_pos hp,if_neg hp',he]
      exact hab _
    · have hp' : (i.val+1)%2=0 := by omega
      have he : (index (K:=K+1) i.castSucc).val+1=(index (K:=K+1) i.succ).val := by dsimp [index];omega
      simp only [weave,Fin.val_castSucc,Fin.val_succ,if_neg hp,if_pos hp']
      exact hnext _ _ he

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def Pack (E : Bool → α → Prop) (lo hi : α → Finset β) (K : Nat) : Prop :=
  ∃a b : Fin K → α,∃X Y : Fin K → Finset β,
    (∀i,Lib1436Boxes.Box lo hi (a i) (X i) ∧ E true (a i) ∧
      Lib1436Boxes.Box lo hi (b i) (Y i) ∧ E false (b i) ∧ X i⊆Y i) ∧
    ∀i j,i.val+1=j.val → Y i⊆X j

theorem path_of_pack {E : Bool → α → Prop} {lo hi : α → Finset β} {K : Nat}
    (hp : Pack E lo hi K) : ∃S,Lib1436Subset.Path E (fun i j=>lo i⊆hi j) (2*K) S := by
  classical
  obtain ⟨a,b,X,Y,hrow,hnext⟩ := hp
  let lab := weave a b
  let xs := weave X Y
  have hm : Monotone xs := weave_monotone X Y (fun i=>(hrow i).2.2.2.2) hnext
  have hx : ∀i,Lib1436Boxes.Box lo hi (lab i) (xs i) := by
    intro i
    dsimp only [lab,xs,weave]
    split_ifs
    · exact (hrow _).1
    · exact (hrow _).2.2.1
  have he : ∀i,E (Lib1436Subset.shade i.val) (lab i) := by
    intro i
    by_cases hh : i.val % 2=0
    · simpa only [Lib1436Subset.shade,lab,weave,if_pos hh,decide_eq_true hh] using (hrow (index i)).2.1
    · simpa only [Lib1436Subset.shade,lab,weave,if_neg hh,decide_eq_false hh] using (hrow (index i)).2.2.2.1
  refine ⟨Finset.univ.image lab,Lib1436Subset.path_of_ordered lab he ?_⟩
  intro i j hij
  exact (hx i).1.trans ((hm hij).trans (hx j).2)

theorem pack_of_path {E : Bool → α → Prop} {lo hi : α → Finset β} {K : Nat} {S : Finset α}
    (hp : Lib1436Subset.Path E (fun i j=>lo i⊆hi j) (2*K) S) : Pack E lo hi K := by
  classical
  obtain ⟨lab,_,he,hr⟩ := Lib1436Subset.ordered_of_path hp
  obtain ⟨X,hm,hx⟩ := (Lib1436Boxes.ordered_iff_realizable lo hi lab).mp hr
  refine ⟨(fun i=>lab (even i)),(fun i=>lab (odd i)),(fun i=>X (even i)),(fun i=>X (odd i)),?_,?_⟩
  · intro i
    refine ⟨hx _,?_,hx _,?_,hm (by change 2*i.val ≤ 2*i.val+1;omega)⟩
    · have hs : Lib1436Subset.shade (even i).val=true := by simp [Lib1436Subset.shade,even,Nat.mul_mod]
      simpa only [hs] using he (even i)
    · have hs : Lib1436Subset.shade (odd i).val=false := by simp [Lib1436Subset.shade,odd,Nat.add_mod,Nat.mul_mod]
      simpa only [hs] using he (odd i)
  · intro i j hij
    apply hm
    change 2*i.val+1 ≤ 2*j.val
    omega

theorem pack_iff_path {E : Bool → α → Prop} {lo hi : α → Finset β} {K : Nat} :
    Pack E lo hi K ↔ ∃S,Lib1436Subset.Path E (fun i j=>lo i⊆hi j) (2*K) S :=
  ⟨path_of_pack,fun ⟨_,hp⟩=>pack_of_path hp⟩

end Lib1436Pairs

namespace Lib1436Pairs
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem pack_iff_bad_or_dp {E : Bool → α → Prop} {lo hi : α → Finset β} {K : Nat}
    (hK : 0 < K) : Pack E lo hi K ↔ Lib1436Boxes.Bad E lo hi ∨
      ∃S,Lib1436Subset.DP E (fun i j=>lo i⊆hi j) S ∧ 2*K ≤ S.card := by
  classical
  constructor
  · intro hp
    by_cases hb : Lib1436Boxes.Bad E lo hi
    · exact Or.inl hb
    · right
      have hc : ¬Lib1436Subset.Collision E (fun i j=>lo i⊆hi j) :=
        fun hh=>hb ((Lib1436Boxes.collision_iff_bad E lo hi).mp hh)
      obtain ⟨S,hS⟩ := path_of_pack hp
      exact ⟨S,Lib1436Subset.dp_of_path hc hS,by rw [Lib1436Subset.path_card hc hS]⟩
  · rintro (⟨i,j,X,hi,hj,hXi,hXj⟩ | ⟨S,hS,hcard⟩)
    · exact ⟨(fun _=>i),(fun _=>j),(fun _=>X),(fun _=>X),
        (fun _=>⟨hXi,hi,hXj,hj,Finset.Subset.refl _⟩),fun _ _ _=>Finset.Subset.refl _⟩
    · obtain ⟨T,_,hT⟩ := Lib1436Subset.path_prefix (Lib1436Subset.path_of_dp hS) hcard
      exact pack_of_path hT

theorem no_pack_iff {E : Bool → α → Prop} {lo hi : α → Finset β} {K : Nat}
    (hK : 0 < K) : (¬Pack E lo hi K) ↔ ¬Lib1436Boxes.Bad E lo hi ∧
      ∀S,Lib1436Subset.DP E (fun i j=>lo i⊆hi j) S → S.card < 2*K := by
  rw [pack_iff_bad_or_dp hK]
  push_neg
  rfl

end Lib1436Pairs

namespace Lib1436Criterion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
variable {α : Type} [DecidableEq α]

noncomputable def xs {r : Nat} (z : α × Finset (Fin r)) : Fin r → Bool := by
  classical
  exact fun j=>decide (j∈z.2)

def Pos {r : Nat} (E : Bool → α → Prop) (lo hi : α → Finset (Fin r))
    (z : α × Finset (Fin r)) (_ : Fin 1) : Prop := Lib1436Boxes.Box lo hi z.1 z.2 ∧ E true z.1

def Neg {r : Nat} (E : Bool → α → Prop) (lo hi : α → Finset (Fin r))
    (z : α × Finset (Fin r)) (_ : Fin 1) : Prop := Lib1436Boxes.Box lo hi z.1 z.2 ∧ E false z.1

noncomputable def Fits {r : Nat} (E : Bool → α → Prop) (lo hi : α → Finset (Fin r)) (b : Nat) : Prop :=
  ∃(C : Circuit)(p : Fin 1 → Fin (r+2+C.size)),FanInTwo C ∧ ReadsBack (r+2) C ∧
    C.output < r+2+C.size ∧ notCount C ≤ b ∧
    ∀z j,(Pos E lo hi z j → (C.wires (List.ofFn (xs z)++[false,true])).getD (p j).val false=true) ∧
      (Neg E lo hi z j → (C.wires (List.ofFn (xs z)++[false,true])).getD (p j).val false=false)

theorem xs_le_iff {r : Nat} (a b : α × Finset (Fin r)) : xs a ≤ xs b ↔ a.2⊆b.2 := by
  classical
  constructor
  · intro hh j hj
    exact of_decide_eq_true (hh j (decide_eq_true hj))
  · intro hh j hj
    exact decide_eq_true (hh (of_decide_eq_true hj))

theorem fits_iff_no_pack {r : Nat} (E : Bool → α → Prop) (lo hi : α → Finset (Fin r)) (b : Nat) :
    Fits E lo hi b ↔ ¬Lib1436Pairs.Pack E lo hi (2^b) := by
  classical
  unfold Fits
  rw [Lib1431Partial.fits_iff]
  apply not_congr
  constructor
  · rintro ⟨a,c,hac,hnext⟩
    refine ⟨(fun i=>(a i).1),(fun i=>(c i).1),(fun i=>(a i).2),(fun i=>(c i).2),?_,?_⟩
    · intro i
      obtain ⟨hle,j,hp,hn⟩ := hac i
      exact ⟨hp.1,hp.2,hn.1,hn.2,(xs_le_iff _ _).mp hle⟩
    · intro i j hij
      exact (xs_le_iff _ _).mp (hnext i j hij)
  · rintro ⟨a,c,X,Y,hac,hnext⟩
    refine ⟨(fun i=>(a i,X i)),(fun i=>(c i,Y i)),?_,?_⟩
    · intro i
      obtain ⟨hXi,hei,hYi,hfi,hXY⟩ := hac i
      exact ⟨(xs_le_iff _ _).mpr hXY,0,⟨hXi,hei⟩,⟨hYi,hfi⟩⟩
    · intro i j hij
      exact (xs_le_iff _ _).mpr (hnext i j hij)

theorem fits_iff {r : Nat} (E : Bool → α → Prop) (lo hi : α → Finset (Fin r)) (b : Nat) :
    Fits E lo hi b ↔ ¬Lib1436Boxes.Bad E lo hi ∧
      ∀S,Lib1436Subset.DP E (fun i j=>lo i⊆hi j) S → S.card < 2*(2^b) := by
  rw [fits_iff_no_pack,Lib1436Pairs.no_pack_iff (Nat.two_pow_pos b)]

end Lib1436Criterion

namespace Lib1436Criterion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
variable {α : Type} [DecidableEq α]

noncomputable def input {r : Nat} (X : Finset (Fin r)) : List Bool := by
  classical
  exact List.ofFn (fun j=>decide (j∈X))++[false,true]

noncomputable def ScalarFits {r : Nat} (E : Bool → α → Prop) (lo hi : α → Finset (Fin r)) (b : Nat) : Prop :=
  ∃C : Circuit,FanInTwo C ∧ ReadsBack (r+2) C ∧ C.output < r+2+C.size ∧ notCount C ≤ b ∧
    ∀i X,Lib1436Boxes.Box lo hi i X → ∀v,E v i → C.eval (input X)=v

theorem scalar_iff_fits {r : Nat} (E : Bool → α → Prop) (lo hi : α → Finset (Fin r)) (b : Nat) :
    ScalarFits E lo hi b ↔ Fits E lo hi b := by
  classical
  constructor
  · rintro ⟨C,hf,hr,ho,hn,hsem⟩
    refine ⟨C,(fun _=>⟨C.output,ho⟩),hf,hr,ho,hn,?_⟩
    intro z j
    constructor
    · rintro ⟨hbox,he⟩
      exact hsem z.1 z.2 hbox true he
    · rintro ⟨hbox,he⟩
      exact hsem z.1 z.2 hbox false he
  · rintro ⟨C,p,hf,hr,ho,hn,hsem⟩
    let D : Circuit := ⟨C.gates,(p 0).val⟩
    refine ⟨D,hf,hr,(p 0).isLt,hn,?_⟩
    intro i X hbox v he
    cases v with
    | false => exact (hsem (i,X) 0).2 ⟨hbox,he⟩
    | true => exact (hsem (i,X) 0).1 ⟨hbox,he⟩

theorem scalar_iff {r : Nat} (E : Bool → α → Prop) (lo hi : α → Finset (Fin r)) (b : Nat) :
    ScalarFits E lo hi b ↔ ¬Lib1436Boxes.Bad E lo hi ∧
      ∀S,Lib1436Subset.DP E (fun i j=>lo i⊆hi j) S → S.card < 2*(2^b) := by
  rw [scalar_iff_fits,fits_iff]

end Lib1436Criterion

namespace Lib1436Nat
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

noncomputable def lift (r : Nat) (X : Finset Nat) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun j=>j.val∈X)

def lower {r : Nat} (X : Finset (Fin r)) : Finset Nat := X.image Fin.val

@[simp] theorem mem_lift {r : Nat} {X : Finset Nat} {j : Fin r} : j∈lift r X ↔ j.val∈X := by
  classical
  simp [lift]

@[simp] theorem val_mem_lower {r : Nat} {X : Finset (Fin r)} {j : Fin r} : j.val∈lower X ↔ j∈X := by
  constructor
  · intro h
    obtain ⟨a,ha,haj⟩ := Finset.mem_image.mp h
    exact Fin.ext haj ▸ ha
  · intro h
    exact Finset.mem_image.mpr ⟨j,h,rfl⟩

theorem lower_bound {r : Nat} (X : Finset (Fin r)) : lower X ⊆ Finset.range r := by
  intro j hj
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_range.mpr i.isLt

@[simp] theorem lift_lower {r : Nat} (X : Finset (Fin r)) : lift r (lower X)=X := by
  ext j
  simp

theorem lower_lift {r : Nat} (X : Finset Nat) (hX : X⊆Finset.range r) : lower (lift r X)=X := by
  ext j
  constructor
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact mem_lift.mp hi
  · intro hj
    exact Finset.mem_image.mpr ⟨⟨j,Finset.mem_range.mp (hX hj)⟩,mem_lift.mpr hj,rfl⟩

theorem lift_subset_iff {r : Nat} {X Y : Finset Nat} (hX : X⊆Finset.range r) :
    lift r X⊆lift r Y ↔ X⊆Y := by
  constructor
  · intro h j hj
    exact mem_lift.mp (h (mem_lift.mpr (show (⟨j,Finset.mem_range.mp (hX hj)⟩ : Fin r).val∈X from hj)))
  · intro h j hj
    exact mem_lift.mpr (h (mem_lift.mp hj))

noncomputable def bits (r : Nat) (X : Finset Nat) : List Bool := by
  classical
  exact List.ofFn (fun j : Fin r=>decide (j.val∈X))++[false,true]

theorem input_lift (r : Nat) (X : Finset Nat) : Lib1436Criterion.input (lift r X)=bits r X := by
  classical
  simp only [Lib1436Criterion.input,bits,mem_lift]

theorem input_lower {r : Nat} (X : Finset (Fin r)) : Lib1436Criterion.input X=bits r (lower X) := by
  rw [←input_lift,lift_lower]

noncomputable def Fit {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat) (b : Nat) : Prop :=
  ∃C : Circuit,FanInTwo C ∧ ReadsBack (r+2) C ∧ C.output < r+2+C.size ∧ notCount C≤b ∧
    ∀X⊆Finset.range r,∀i : Fin m,Finset.range r \ Z i⊆X→X⊆O i→∀v,i.val∈E v→C.eval (bits r X)=v

theorem fit_iff_scalar {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat) (b : Nat) :
    Fit (r:=r) Z O E b ↔ Lib1436Criterion.ScalarFits (fun v i=>i.val∈E v)
      (fun i=>lift r (Finset.range r \ Z i)) (fun i=>lift r (O i)) b := by
  classical
  constructor
  · rintro ⟨C,hf,hr,ho,hn,hsem⟩
    refine ⟨C,hf,hr,ho,hn,?_⟩
    intro i X hx v hv
    rw [input_lower]
    apply hsem (lower X) (lower_bound X) i
    · apply (lift_subset_iff (Finset.sdiff_subset)).mp
      simpa only [lift_lower] using hx.1
    · intro j hj
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hj
      exact mem_lift.mp (hx.2 ha)
    · exact hv
  · rintro ⟨C,hf,hr,ho,hn,hsem⟩
    refine ⟨C,hf,hr,ho,hn,?_⟩
    intro X hX i hlo hhi v hv
    rw [←input_lift]
    exact hsem i (lift r X) ⟨(lift_subset_iff Finset.sdiff_subset).mpr hlo,
      (lift_subset_iff hX).mpr hhi⟩ v hv

end Lib1436Nat

namespace Lib1436Threshold
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def T (E : Bool → α → Prop) (lo hi : α → Finset β) (ell : Nat) (X : Finset β) : Prop :=
  ∃S,Lib1436Subset.DP E (fun i j=>lo i⊆hi j) S ∧ (∀i∈S,lo i⊆X) ∧ ell ≤ S.card

theorem zero (E : Bool → α → Prop) (lo hi : α → Finset β) (X : Finset β) : T E lo hi 0 X := by
  exact ⟨∅,Lib1436Subset.DP.nil,by simp,by simp⟩

theorem antitone (E : Bool → α → Prop) (lo hi : α → Finset β) (X : Finset β) :
    Antitone (fun ell=>T E lo hi ell X) := by
  intro i j hij hT
  obtain ⟨S,hS,hcap,hj⟩ := hT
  exact ⟨S,hS,hcap,hij.trans hj⟩

theorem monotone (E : Bool → α → Prop) (lo hi : α → Finset β) (ell : Nat) :
    Monotone (T E lo hi ell) := by
  intro X Y hXY hT
  obtain ⟨S,hS,hcap,hcard⟩ := hT
  exact ⟨S,hS,fun i hi=>(hcap i hi).trans hXY,hcard⟩

theorem extend {E : Bool → α → Prop} {lo hi : α → Finset β} {ell : Nat} {X : Finset β}
    (hnoc : ¬Lib1436Subset.Collision E (fun i j=>lo i⊆hi j))
    (j : α) (hj : E (Lib1436Subset.shade ell) j) (hbox : Lib1436Boxes.Box lo hi j X)
    (hT : T E lo hi ell X) : T E lo hi (ell+1) X := by
  classical
  obtain ⟨S,hS,hcap,hcard⟩ := hT
  obtain ⟨U,hUS,hU⟩ := Lib1436Subset.path_prefix (Lib1436Subset.path_of_dp hS) hcard
  have hc : ∀i∈insert j U,lo i⊆X := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hbox.1
    · exact hcap i (hUS hi)
  have hp := Lib1436Subset.Path.step j hU hj (fun i hi=>(hc i hi).trans hbox.2)
  exact ⟨insert j U,Lib1436Subset.dp_of_path hnoc hp,hc,by rw [Lib1436Subset.path_card hnoc hp]⟩

theorem boundary (P : Nat → Prop) (d : Nat) (h0 : P 0) (hend : ¬P (d+1)) :
    ∃q,q ≤ d ∧ P q ∧ ¬P (q+1) := by
  induction d with
  | zero => exact ⟨0,le_refl _,h0,hend⟩
  | succ d ih =>
    by_cases hp : P (d+1)
    · exact ⟨d+1,le_refl _,hp,hend⟩
    · obtain ⟨q,hq,hP,hN⟩ := ih hp
      exact ⟨q,by omega,hP,hN⟩

def Read (E : Bool → α → Prop) (lo hi : α → Finset β) (d : Nat) (X : Finset β) : Prop :=
  T E lo hi (2*d+1) X ∨ ∃q : Fin d,T E lo hi (2*q.val+1) X ∧ ¬T E lo hi (2*q.val+2) X

theorem read_correct {E : Bool → α → Prop} {lo hi : α → Finset β} (d : Nat) (X : Finset β)
    (hnoc : ¬Lib1436Subset.Collision E (fun i j=>lo i⊆hi j))
    (hend : ¬T E lo hi (2*d+2) X) (j : α) (v : Bool) (hj : E v j)
    (hbox : Lib1436Boxes.Box lo hi j X) : Read E lo hi d X ↔ v=true := by
  classical
  cases v with
  | false =>
    constructor
    · rintro (hT | ⟨q,hT,hN⟩)
      · have he : E (Lib1436Subset.shade (2*d+1)) j := by
          simpa [Lib1436Subset.shade,Nat.add_mod,Nat.mul_mod] using hj
        exact False.elim (hend (extend hnoc j he hbox hT))
      · have he : E (Lib1436Subset.shade (2*q.val+1)) j := by
          simpa [Lib1436Subset.shade,Nat.add_mod,Nat.mul_mod] using hj
        exact False.elim (hN (extend hnoc j he hbox hT))
    · intro hh
      cases hh
  | true =>
    constructor
    · intro _;rfl
    · intro _
      have hlast : ¬T E lo hi (2*(d+1)) X := by simpa only [Nat.mul_add,Nat.mul_one] using hend
      obtain ⟨q,hq,hT,hN⟩ := boundary (fun q=>T E lo hi (2*q) X) d (zero E lo hi X) hlast
      have he : E (Lib1436Subset.shade (2*q)) j := by simpa [Lib1436Subset.shade,Nat.mul_mod] using hj
      have hp := extend hnoc j he hbox hT
      by_cases hqd : q=d
      · subst q;exact Or.inl hp
      · exact Or.inr ⟨⟨q,by omega⟩,hp,by simpa only [Nat.mul_add,Nat.mul_one] using hN⟩

def depthCap (m b : Nat) : Nat := min (m/2) (2^b-1)

theorem depthCap_lt (m b : Nat) : depthCap m b < 2^b := by
  have hp := Nat.two_pow_pos b
  have hh := Nat.min_le_right (m/2) (2^b-1)
  unfold depthCap
  omega

theorem terminal {m : Nat} {E : Bool → Fin m → Prop} {lo hi : Fin m → Finset β} (b : Nat)
    (hbound : ∀S,Lib1436Subset.DP E (fun i j=>lo i⊆hi j) S → S.card < 2*(2^b)) (X : Finset β) :
    ¬T E lo hi (2*depthCap m b+2) X := by
  rintro ⟨S,hS,_,hcard⟩
  have hm : S.card ≤ m := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hb := hbound S hS
  have hp := Nat.two_pow_pos b
  unfold depthCap at hcard
  by_cases hc : m/2 ≤ 2^b-1
  · rw [Nat.min_eq_left hc] at hcard
    omega
  · rw [Nat.min_eq_right (by omega : 2^b-1 ≤ m/2)] at hcard
    omega

end Lib1436Threshold

namespace Lib1436Compile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

theorem fold_and_true (inputs : List Nat) (bits : Nat → Bool) (base : Bool) :
    inputs.foldl (fun b i => b && bits i) base = true ↔
      base = true ∧ ∀ i ∈ inputs,bits i = true := by
  induction inputs generalizing base with
  | nil => simp
  | cons i rest ih =>
    simp only [List.foldl_cons,ih,Bool.and_eq_true,List.mem_cons,forall_eq_or_imp,and_assoc]

theorem append_and_rows {n k : ℕ} (C : Circuit) (rows : Fin k → List ℕ)
    (basis : FanInTwo C) (reads : ReadsBack (n+2) C)
    (rowValid : ∀ i a, a ∈ rows i → a < nextWire (n+2) C) :
    ∃ (D : Circuit) (out : Fin k → ℕ), FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D = notCount C ∧ D.size = C.size + (∑ i : Fin k, (rows i).length) ∧
      (∀ i, out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i, value D (withConstants x) (out i) = true ↔
        ∀ a ∈ rows i, value C (withConstants x) a = true := by
  induction k generalizing C with
  | zero =>
    exact ⟨C,Fin.elim0,basis,reads,List.prefix_rfl,rfl,by simp,fun i => Fin.elim0 i,
      fun _ i => Fin.elim0 i⟩
  | succ k ih =>
    let first := foldBinary (n+2) true C (n+1) (rows 0)
    have zeroLive : n+1 < nextWire (n+2) C := by unfold nextWire; omega
    obtain ⟨hBasis,hReads,hLive,hSize,hNot,hEval⟩ :=
      foldBinary_spec (n+2) true C (n+1) (rows 0) basis reads zeroLive (rowValid 0)
    have firstPrefix : C.gates <+: first.1.gates := by
      unfold first
      apply foldBinary_prefix
    have tailValid (i : Fin k) (a : ℕ) (ha : a ∈ rows i.succ) :
        a < nextWire (n+2) first.1 :=
      (rowValid i.succ a ha).trans_le (nextWire_le_of_prefix firstPrefix)
    obtain ⟨D,tail,dBasis,dReads,dPrefix,dNot,dSize,dLive,dEval⟩ :=
      ih first.1 (fun i => rows i.succ) hBasis hReads tailValid
    let out : Fin (k+1) → ℕ := Fin.cases first.2 tail
    refine ⟨D,out,dBasis,dReads,firstPrefix.trans dPrefix,dNot.trans hNot,?_,?_,?_⟩
    · rw [dSize,Fin.sum_univ_succ]
      change first.1.size = C.size + (rows 0).length at hSize
      rw [hSize,Nat.add_assoc]
    · intro i
      refine Fin.cases ?_ (fun j => dLive j) i
      exact hLive.trans_le (nextWire_le_of_prefix dPrefix)
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · change value D (withConstants x) first.2 = true ↔ _
        have live : first.2 < nextWire (withConstants x).length first.1 := by
          simpa only [withConstants_length] using hLive
        rw [value_of_prefix dPrefix live]
        change value (foldBinary (n+2) true C (n+1) (rows 0)).1 (withConstants x)
          (foldBinary (n+2) true C (n+1) (rows 0)).2 = true ↔ _
        rw [(hEval (withConstants x) (withConstants_length x)).2,true_value]
        simp only [binaryValue,ite_true,fold_and_true,true_and]
      · change value D (withConstants x) (tail j) = true ↔ _
        rw [dEval x j]
        constructor
        · intro H a mem
          exact ((hEval (withConstants x) (withConstants_length x)).1 a
            (rowValid j.succ a mem)).symm.trans (H a mem)
        · intro H a mem
          exact ((hEval (withConstants x) (withConstants_length x)).1 a
            (rowValid j.succ a mem)).trans (H a mem)

end Lib1436Compile

namespace Lib1436Compile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

theorem append_or_and_bank {n k r : Nat} (C : Circuit)
    (left right : Fin k → Fin r → Nat) (hf : FanInTwo C) (hr : ReadsBack (n+2) C)
    (hl : ∀i j,left i j < nextWire (n+2) C)
    (hh : ∀i j,right i j < nextWire (n+2) C) :
    ∃ (D : Circuit) (out : Fin k → Nat),FanInTwo D ∧ ReadsBack (n+2) D ∧
      C.gates <+: D.gates ∧ notCount D=notCount C ∧ D.size=C.size+2*k*r ∧
      (∀i,out i < nextWire (n+2) D) ∧
      ∀ (x : Input n) i,value D (withConstants x) (out i)=true ↔
        ∀j,value C (withConstants x) (left i j)=true ∨ value C (withConstants x) (right i j)=true := by
  classical
  let gate : Fin (k*r) → Gate := fun z =>
    let ij := (finProdFinEquiv : Fin k × Fin r ≃ Fin (k*r)).symm z
    ⟨.or,[left ij.1 ij.2,right ij.1 ij.2]⟩
  let A := appendFamily C gate
  have ap : C.gates <+: A.gates := appendFamily_prefix C gate
  have af : FanInTwo A := by
    apply appendFamily_fanInTwo hf
    intro z
    change GateOp.or ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ _ ≤ 2
    constructor
    · simp
    · simp [gate]
  have areads : ∀ z i,i ∈ (gate z).inputs → i < nextWire (n+2) C := by
    intro z i hi
    simp only [gate,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · exact hl _ _
    · exact hh _ _
  have ar : ReadsBack (n+2) A := appendFamily_readsBack hr areads
  have an : notCount A=notCount C := appendFamily_notCount_eq (by intro z; simp [gate])
  have az : A.size=C.size+k*r := appendFamily_size C gate
  let wire : Fin k → Fin r → Nat := fun i j =>
    nextWire (n+2) C+(finProdFinEquiv (i,j)).val
  have wl : ∀i j,wire i j < nextWire (n+2) A := by
    intro i j
    have H := (finProdFinEquiv (i,j)).isLt
    dsimp [wire,nextWire]
    rw [az]
    omega
  have wv : ∀ (x : Input n) i j,value A (withConstants x) (wire i j) =
      (value C (withConstants x) (left i j) || value C (withConstants x) (right i j)) := by
    intro x i j
    have H := appendFamily_new (C:=C) (gate:=gate) (x:=withConstants x)
      (by simpa only [withConstants_length] using areads) (finProdFinEquiv (i,j))
    simpa only [withConstants_length,gate,Equiv.symm_apply_apply,List.map_cons,List.map_nil,
      GateOp.eval,List.any_cons,List.any_nil,Bool.or_false,id_eq,A,wire] using H
  let rows : Fin k → List Nat := fun i => List.ofFn (wire i)
  obtain ⟨D,out,df,dr,dp,dn,dz,dl,dv⟩ := append_and_rows A rows af ar (by
    intro i a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact wl i j)
  refine ⟨D,out,df,dr,ap.trans dp,dn.trans an,?_,dl,?_⟩
  · rw [dz,az]
    simp only [rows,List.length_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul]
    ring
  · intro x i
    rw [dv]
    constructor
    · intro H j
      have H' := H (wire i j) (List.mem_ofFn.mpr ⟨j,rfl⟩)
      rw [wv] at H'
      simpa only [Bool.or_eq_true] using H'
    · intro H a ha
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
      rw [wv]
      simpa only [Bool.or_eq_true] using H j

end Lib1436Compile

namespace Lib1436Compile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

theorem keep {n : Nat} {C D : Circuit} (ex : C.gates <+: D.gates)
    {i : Nat} (hi : i < nextWire (n+2) C) (x : Input n) :
    value D (withConstants x) i = value C (withConstants x) i :=
  value_of_prefix ex (by simpa only [withConstants_length] using hi)

set_option maxHeartbeats 1200000 in
theorem append_subset_step {n m : Nat} (C : Circuit) (S : Finset (Fin m))
    (oldInc rel previous enabled : Fin m → Nat) (oldCap capOne : Nat)
    (hf : FanInTwo C) (hr : ReadsBack (n+2) C)
    (ho : ∀j,oldInc j < nextWire (n+2) C) (hrel : ∀j,rel j < nextWire (n+2) C)
    (hp : ∀j,previous j < nextWire (n+2) C) (he : ∀j,enabled j < nextWire (n+2) C)
    (hc : oldCap < nextWire (n+2) C) (hco : capOne < nextWire (n+2) C) :
    ∃ (D : Circuit) (inc : Fin m → Nat) (dp cap : Nat),
      FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧ notCount D=notCount C ∧
      D.size=C.size+5*m+S.card+2 ∧
      (∀j,inc j < nextWire (n+2) D) ∧ dp < nextWire (n+2) D ∧ cap < nextWire (n+2) D ∧
      (∀(x : Input n) j,value D (withConstants x) (inc j)=true ↔
        value C (withConstants x) (oldInc j)=true ∧ value C (withConstants x) (rel j)=true) ∧
      (∀x : Input n,value D (withConstants x) dp=true ↔ ∃j∈S,
        value C (withConstants x) (previous j)=true ∧ value C (withConstants x) (enabled j)=true ∧
        value C (withConstants x) (oldInc j)=true ∧ value C (withConstants x) (rel j)=true) ∧
      (∀x : Input n,value D (withConstants x) cap=true ↔
        value C (withConstants x) oldCap=true ∧ value C (withConstants x) capOne=true) := by
  classical
  let rowA : Fin m → List Nat := fun j => [oldInc j,rel j]
  obtain ⟨A,inc,af,ar,ap,an,az,al,av⟩ := append_and_rows C rowA hf hr (by
    intro j a ha
    simp only [rowA,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact ho j
    · exact hrel j)
  have av' (x : Input n) j : value A (withConstants x) (inc j)=true ↔
      value C (withConstants x) (oldInc j)=true ∧ value C (withConstants x) (rel j)=true := by
    simpa [rowA] using av x j
  let rowB : Fin m → List Nat := fun j => [previous j,enabled j,inc j]
  obtain ⟨B,term,bf,br,bp,bn,bz,bl,bv⟩ := append_and_rows A rowB af ar (by
    intro j a ha
    simp only [rowB,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact (hp j).trans_le (nextWire_le_of_prefix ap)
    · exact (he j).trans_le (nextWire_le_of_prefix ap)
    · exact al j)
  have bv' (x : Input n) j : value B (withConstants x) (term j)=true ↔
      value C (withConstants x) (previous j)=true ∧ value C (withConstants x) (enabled j)=true ∧
      value C (withConstants x) (oldInc j)=true ∧ value C (withConstants x) (rel j)=true := by
    have H := bv x j
    simpa only [rowB,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      keep ap (hp j) x,keep ap (he j) x,av'] using H
  let rowG : Fin 1 → List Nat := fun _ => S.toList.map term
  obtain ⟨G,dp,gf,gr,gp,gn,gz,gl,gv⟩ := append_or_rows B rowG bf br (by
    intro j a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact bl i)
  let rowD : Fin 1 → List Nat := fun _ => [oldCap,capOne]
  have cp : C.gates <+: G.gates := ap.trans (bp.trans gp)
  obtain ⟨D,cap,df,dr,dpp,dn,dz,dl,dv⟩ := append_and_rows G rowD gf gr (by
    intro j a ha
    simp only [rowD,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact hc.trans_le (nextWire_le_of_prefix cp)
    · exact hco.trans_le (nextWire_le_of_prefix cp))
  have ad : A.gates <+: D.gates := bp.trans (gp.trans dpp)
  refine ⟨D,inc,dp 0,cap 0,df,dr,ap.trans ad,?_,?_,?_,?_,dl 0,?_,?_,?_⟩
  · exact dn.trans (gn.trans (bn.trans an))
  · rw [dz,gz,bz,az]
    simp only [rowD,rowG,rowB,rowA,List.length_cons,List.length_nil,List.length_map,
      Finset.length_toList,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul]
    omega
  · intro j
    exact (al j).trans_le (nextWire_le_of_prefix ad)
  · exact (gl 0).trans_le (nextWire_le_of_prefix dpp)
  · intro x j
    rw [keep ad (al j) x]
    exact av' x j
  · intro x
    rw [keep dpp (gl 0) x,gv]
    constructor
    · rintro ⟨a,ha,hv⟩
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
      exact ⟨j,Finset.mem_toList.mp hj,(bv' x j).mp hv⟩
    · rintro ⟨j,hj,hv⟩
      exact ⟨term j,List.mem_map.mpr ⟨j,Finset.mem_toList.mpr hj,rfl⟩,(bv' x j).mpr hv⟩
  · intro x
    have H := dv x 0
    simpa only [rowD,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      keep cp hc x,keep cp hco x] using H

end Lib1436Compile

namespace Lib1436Compile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

structure Cache {n m : Nat} (C : Circuit)
    (E : Input n → Bool → Fin m → Prop) (R : Input n → Fin m → Fin m → Prop)
    (F : Input n → Fin m → Prop) (done : Finset (Finset (Fin m))) where
  circuit : Circuit
  dp : Finset (Fin m) → Nat
  incoming : Finset (Fin m) → Fin m → Nat
  cap : Finset (Fin m) → Nat
  fan : FanInTwo circuit
  reads : ReadsBack (n+2) circuit
  initial_prefix : C.gates <+: circuit.gates
  nots : notCount circuit=notCount C
  size : circuit.size ≤ C.size+(6*m+2)*done.card
  dp_live : ∀S,dp S < nextWire (n+2) circuit
  incoming_live : ∀S j,incoming S j < nextWire (n+2) circuit
  cap_live : ∀S,cap S < nextWire (n+2) circuit
  dp_value : ∀(x : Input n) S,S∈done →
    (value circuit (withConstants x) (dp S)=true ↔ Lib1436Subset.DP (E x) (R x) S)
  incoming_value : ∀(x : Input n) S,S∈done → ∀j,
    (value circuit (withConstants x) (incoming S j)=true ↔ ∀i∈S,R x i j)
  cap_value : ∀(x : Input n) S,S∈done →
    (value circuit (withConstants x) (cap S)=true ↔ ∀i∈S,F x i)

theorem cache_empty {n m : Nat} (C : Circuit)
    (E : Input n → Bool → Fin m → Prop) (R : Input n → Fin m → Fin m → Prop)
    (F : Input n → Fin m → Prop) (hf : FanInTwo C) (hr : ReadsBack (n+2) C) :
    Nonempty (Cache C E R F ∅) := by
  refine ⟨⟨C,fun _=>n+1,fun _ _=>n+1,fun _=>n+1,hf,hr,List.prefix_rfl,rfl,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · simp
  · intro S; unfold nextWire; omega
  · intro S j; unfold nextWire; omega
  · intro S; unfold nextWire; omega
  · intro x S hS; exact (Finset.notMem_empty S hS).elim
  · intro x S hS; exact (Finset.notMem_empty S hS).elim
  · intro x S hS; exact (Finset.notMem_empty S hS).elim

end Lib1436Compile

namespace Lib1436Compile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

set_option maxHeartbeats 1200000 in
theorem cache_add {n m : Nat} {C : Circuit}
    {E : Input n → Bool → Fin m → Prop} {R : Input n → Fin m → Fin m → Prop}
    {F : Input n → Fin m → Prop} {done : Finset (Finset (Fin m))}
    (K : Cache C E R F done) (S : Finset (Fin m)) (hs : S ∉ done)
    (D : Circuit) (dp cap : Nat) (inc : Fin m → Nat)
    (hf : FanInTwo D) (hr : ReadsBack (n+2) D) (ex : K.circuit.gates <+: D.gates)
    (hn : notCount D=notCount K.circuit) (hz : D.size ≤ K.circuit.size+(6*m+2))
    (hdp : dp < nextWire (n+2) D) (hcap : cap < nextWire (n+2) D)
    (hinc : ∀j,inc j < nextWire (n+2) D)
    (vdp : ∀x : Input n,value D (withConstants x) dp=true ↔ Lib1436Subset.DP (E x) (R x) S)
    (vinc : ∀(x : Input n) j,value D (withConstants x) (inc j)=true ↔ ∀i∈S,R x i j)
    (vcap : ∀x : Input n,value D (withConstants x) cap=true ↔ ∀i∈S,F x i) :
    Nonempty (Cache C E R F (insert S done)) := by
  classical
  refine ⟨{
    circuit:=D, dp:=(fun T=>if T=S then dp else K.dp T),
    incoming:=(fun T j=>if T=S then inc j else K.incoming T j),
    cap:=(fun T=>if T=S then cap else K.cap T),
    fan:=hf,reads:=hr,initial_prefix:=K.initial_prefix.trans ex,nots:=hn.trans K.nots,
    size:=?_,dp_live:=?_,incoming_live:=?_,cap_live:=?_,dp_value:=?_,incoming_value:=?_,cap_value:=?_ }⟩
  · rw [Finset.card_insert_of_notMem hs,Nat.mul_add,Nat.mul_one]
    have H := K.size
    omega
  · intro T
    split
    · exact hdp
    · exact (K.dp_live T).trans_le (nextWire_le_of_prefix ex)
  · intro T j
    split
    · exact hinc j
    · exact (K.incoming_live T j).trans_le (nextWire_le_of_prefix ex)
  · intro T
    split
    · exact hcap
    · exact (K.cap_live T).trans_le (nextWire_le_of_prefix ex)
  · intro x T hT
    by_cases he : T=S
    · subst T; simpa using vdp x
    · simp only [if_neg he]
      rw [keep ex (K.dp_live T) x]
      exact K.dp_value x T ((Finset.mem_insert.mp hT).resolve_left he)
  · intro x T hT j
    by_cases he : T=S
    · subst T; simpa using vinc x j
    · simp only [if_neg he]
      rw [keep ex (K.incoming_live T j) x]
      exact K.incoming_value x T ((Finset.mem_insert.mp hT).resolve_left he) j
  · intro x T hT
    by_cases he : T=S
    · subst T; simpa using vcap x
    · simp only [if_neg he]
      rw [keep ex (K.cap_live T) x]
      exact K.cap_value x T ((Finset.mem_insert.mp hT).resolve_left he)

set_option maxHeartbeats 1600000 in
theorem cache_extend {n m : Nat} {C : Circuit}
    {E : Input n → Bool → Fin m → Prop} {R : Input n → Fin m → Fin m → Prop}
    {F : Input n → Fin m → Prop} {done : Finset (Finset (Fin m))}
    (K : Cache C E R F done) (S : Finset (Fin m)) (hs : S ∉ done)
    (herase : ∀j∈S,S.erase j ∈ done)
    (enabled : Bool → Fin m → Nat) (rel : Fin m → Fin m → Nat) (capOne : Fin m → Nat)
    (el : ∀b j,enabled b j < nextWire (n+2) C)
    (rl : ∀i j,rel i j < nextWire (n+2) C)
    (fl : ∀i,capOne i < nextWire (n+2) C)
    (ev : ∀(x : Input n) b j,value C (withConstants x) (enabled b j)=true ↔ E x b j)
    (rv : ∀(x : Input n) i j,value C (withConstants x) (rel i j)=true ↔ R x i j)
    (fv : ∀(x : Input n) i,value C (withConstants x) (capOne i)=true ↔ F x i) :
    Nonempty (Cache C E R F (insert S done)) := by
  classical
  by_cases hzero : S=∅
  · subst S
    apply cache_add K ∅ hs K.circuit (n+1) (n+1) (fun _=>n+1)
      K.fan K.reads List.prefix_rfl rfl (by omega)
      (by unfold nextWire;omega) (by unfold nextWire;omega) (by intro j;unfold nextWire;omega)
    · intro x
      rw [true_value]
      exact ⟨fun _=>Lib1436Subset.DP.nil,fun _=>rfl⟩
    · intro x j
      simp [true_value]
    · intro x
      simp [true_value]
  · obtain ⟨d,hd⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
    let T := S.erase d
    have hT : T∈done := herase d hd
    have reconstruct : insert d T=S := Finset.insert_erase hd
    let shade := Lib1436Subset.shade (S.card-1)
    obtain ⟨D,inc,dp,cap,df,dr,ex,dn,dz,il,dl,cl,iv,pv,cv⟩ :=
      append_subset_step K.circuit S (K.incoming T) (rel d)
        (fun j=>K.dp (S.erase j)) (enabled shade) (K.cap T) (capOne d)
        K.fan K.reads (K.incoming_live T)
        (fun j=>(rl d j).trans_le (nextWire_le_of_prefix K.initial_prefix))
        (fun j=>K.dp_live (S.erase j))
        (fun j=>(el shade j).trans_le (nextWire_le_of_prefix K.initial_prefix))
        (K.cap_live T) ((fl d).trans_le (nextWire_le_of_prefix K.initial_prefix))
    have vi (x : Input n) j : value D (withConstants x) (inc j)=true ↔ ∀i∈S,R x i j := by
      rw [iv,K.incoming_value x T hT j,keep K.initial_prefix (rl d j) x,rv]
      rw [←reconstruct]
      simp only [Finset.mem_insert,forall_eq_or_imp]
      exact and_comm
    have vd (x : Input n) : value D (withConstants x) dp=true ↔ Lib1436Subset.DP (E x) (R x) S := by
      rw [pv,Lib1436Subset.dp_recurrence]
      simp only [hzero,false_or]
      apply exists_congr
      intro j
      apply and_congr_right
      intro hj
      rw [K.dp_value x (S.erase j) (herase j hj),keep K.initial_prefix (el shade j) x,ev,
        K.incoming_value x T hT j,keep K.initial_prefix (rl d j) x,rv]
      apply and_congr_right
      intro _
      apply and_congr_right
      intro _
      rw [←reconstruct]
      simp only [Finset.mem_insert,forall_eq_or_imp]
      exact and_comm
    have vc (x : Input n) : value D (withConstants x) cap=true ↔ ∀i∈S,F x i := by
      rw [cv,K.cap_value x T hT,keep K.initial_prefix (fl d) x,fv]
      rw [←reconstruct]
      simp only [Finset.mem_insert,forall_eq_or_imp]
      exact and_comm
    exact cache_add K S hs D dp cap inc df dr ex dn
      (by rw [dz];have H:=Finset.card_le_univ S;simp only [Fintype.card_fin] at H;omega)
      dl cl il vd vi vc

end Lib1436Compile


namespace Lib1436Topology

theorem enumeration (m : Nat) :
    ∃ e : Fin (2^m) ≃ Finset (Fin m),
      ∀ S j, j ∈ S → (e.symm (S.erase j)).val < (e.symm S).val := by
  classical
  have hc : Fintype.card (Finset (Fin m)) = 2^m := by simp
  let idx : Finset (Fin m) ≃ Fin (2^m) := Fintype.equivFinOfCardEq hc
  let code (S : Finset (Fin m)) : Nat := S.card * 2^m + (idx S).val
  have hinj : Function.Injective code := by
    intro S T h
    have hh := congrArg (fun z => z % 2^m) h
    have he : (idx S).val = (idx T).val := by
      simpa [code, Nat.add_mod, Nat.mod_eq_of_lt (idx S).isLt,
        Nat.mod_eq_of_lt (idx T).isLt] using hh
    exact idx.injective (Fin.ext he)
  have hlt (S : Finset (Fin m)) (j : Fin m) (hj : j ∈ S) :
      code (S.erase j) < code S := by
    have hcard := Finset.card_erase_add_one hj
    have hb := (idx (S.erase j)).isLt
    dsimp only [code]
    nlinarith
  let codes : Finset Nat := Finset.univ.image code
  have hcodes : codes.card = 2^m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    exact hc
  let f : Finset (Fin m) ≃ ↥codes := Equiv.ofBijective
    (fun S => ⟨code S, Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩⟩)
    ⟨by
      intro S T h
      exact hinj (congrArg Subtype.val h), by
      intro z
      obtain ⟨S, _, hz⟩ := Finset.mem_image.mp z.property
      exact ⟨S, Subtype.ext hz⟩⟩
  let ord := codes.orderIsoOfFin hcodes
  let e := ord.toEquiv.trans f.symm
  refine ⟨e, ?_⟩
  intro S j hj
  have hs : f (S.erase j) < f S := by
    change code (S.erase j) < code S
    exact hlt S j hj
  exact ord.symm.strictMono hs

end Lib1436Topology

namespace Lib1436Topology

theorem iterate_powerset {m : Nat}
    (P : Finset (Finset (Fin m)) → Prop)
    (base : P ∅)
    (step : ∀ done S, S ∉ done →
      (∀ j ∈ S, S.erase j ∈ done) → P done → P (insert S done)) :
    P Finset.univ := by
  classical
  obtain ⟨e, he⟩ := enumeration m
  let done (k : Nat) : Finset (Finset (Fin m)) :=
    Finset.univ.filter (fun S => (e.symm S).val < k)
  have hmem (k : Nat) (S : Finset (Fin m)) :
      S ∈ done k ↔ (e.symm S).val < k := by
    simp [done]
  have hzero : done 0 = ∅ := by
    ext S
    simp [done]
  have hall : ∀ k, k ≤ 2^m → P (done k) := by
    intro k
    induction k with
    | zero =>
        intro hk
        rw [hzero]
        exact base
    | succ k ih =>
        intro hk
        have hkn : k < 2^m := by omega
        let S : Finset (Fin m) := e ⟨k, hkn⟩
        have hidx : (e.symm S).val = k := by simp [S]
        have hnew : S ∉ done k := by rw [hmem, hidx]; omega
        have hprev : ∀ j ∈ S, S.erase j ∈ done k := by
          intro j hj
          rw [hmem]
          have hh := he S j hj
          rwa [hidx] at hh
        have hnext : done (k+1) = insert S (done k) := by
          ext T
          rw [hmem, Finset.mem_insert, hmem]
          have hi : (e.symm T).val = k ↔ T = S := by
            constructor
            · intro hh
              have ht : e.symm T = e.symm S := Fin.ext (hh.trans hidx.symm)
              exact e.symm.injective ht
            · intro hh
              subst T
              exact hidx
          rw [← hi]
          omega
        rw [hnext]
        exact step (done k) S hnew hprev (ih (by omega))
  have hlast : done (2^m) = Finset.univ := by
    ext S
    simp only [hmem, Finset.mem_univ, iff_true]
    exact (e.symm S).isLt
  rw [← hlast]
  exact hall (2^m) (le_refl _)

end Lib1436Topology

namespace Lib1436Compile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

theorem cache_all {n m : Nat} (C : Circuit)
    (E : Input n → Bool → Fin m → Prop) (R : Input n → Fin m → Fin m → Prop)
    (F : Input n → Fin m → Prop)
    (hf : FanInTwo C) (hr : ReadsBack (n+2) C)
    (enabled : Bool → Fin m → Nat) (rel : Fin m → Fin m → Nat) (capOne : Fin m → Nat)
    (el : ∀ b j, enabled b j < nextWire (n+2) C)
    (rl : ∀ i j, rel i j < nextWire (n+2) C)
    (fl : ∀ i, capOne i < nextWire (n+2) C)
    (ev : ∀ (x : Input n) b j, value C (withConstants x) (enabled b j)=true ↔ E x b j)
    (rv : ∀ (x : Input n) i j, value C (withConstants x) (rel i j)=true ↔ R x i j)
    (fv : ∀ (x : Input n) i, value C (withConstants x) (capOne i)=true ↔ F x i) :
    Nonempty (Cache C E R F Finset.univ) := by
  apply Lib1436Topology.iterate_powerset (fun done => Nonempty (Cache C E R F done))
  · exact cache_empty C E R F hf hr
  · intro done S hs herase hcache
    obtain ⟨K⟩ := hcache
    exact cache_extend K S hs herase enabled rel capOne el rl fl ev rv fv

end Lib1436Compile

namespace Lib1436Compile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

def cache_lift {n m : Nat} {C : Circuit}
    {E : Input n → Bool → Fin m → Prop} {R : Input n → Fin m → Fin m → Prop}
    {F : Input n → Fin m → Prop} {done : Finset (Finset (Fin m))}
    (K : Cache C E R F done) (D : Circuit) (hf : FanInTwo D) (hr : ReadsBack (n+2) D)
    (ex : K.circuit.gates <+: D.gates) : Cache D E R F done where
  circuit := D
  dp := K.dp
  incoming := K.incoming
  cap := K.cap
  fan := hf
  reads := hr
  initial_prefix := List.prefix_rfl
  nots := rfl
  size := Nat.le_add_right _ _
  dp_live := fun S=>(K.dp_live S).trans_le (nextWire_le_of_prefix ex)
  incoming_live := fun S j=>(K.incoming_live S j).trans_le (nextWire_le_of_prefix ex)
  cap_live := fun S=>(K.cap_live S).trans_le (nextWire_le_of_prefix ex)
  dp_value := by
    intro x S hs
    rw [keep ex (K.dp_live S) x]
    exact K.dp_value x S hs
  incoming_value := by
    intro x S hs j
    rw [keep ex (K.incoming_live S j) x]
    exact K.incoming_value x S hs j
  cap_value := by
    intro x S hs
    rw [keep ex (K.cap_live S) x]
    exact K.cap_value x S hs

end Lib1436Compile

namespace Lib1436Compile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

theorem collision_true_first {m : Nat} (E : Bool → Fin m → Prop) (R : Fin m → Fin m → Prop) :
    Lib1436Subset.Collision E R ↔
      ∃i j,E true i ∧ E false j ∧ R i i ∧ R i j ∧ R j i ∧ R j j := by
  constructor
  · rintro ⟨i,j,b,hi,hj,hii,hij,hji,hjj⟩
    cases b with
    | false => exact ⟨j,i,hj,hi,hjj,hji,hij,hii⟩
    | true => exact ⟨i,j,hi,hj,hii,hij,hji,hjj⟩
  · rintro ⟨i,j,hi,hj,hii,hij,hji,hjj⟩
    exact ⟨i,j,true,hi,hj,hii,hij,hji,hjj⟩

set_option maxHeartbeats 1600000 in
theorem append_failure_bank {n m N : Nat} {C : Circuit}
    {E : Input n → Bool → Fin m → Prop} {R : Input n → Fin m → Fin m → Prop}
    {F : Input n → Fin m → Prop} (K : Cache C E R F Finset.univ)
    (e : Fin N ≃ Finset (Fin m)) (cut : Nat)
    (enabled : Bool → Fin m → Nat) (rel : Fin m → Fin m → Nat)
    (el : ∀b j,enabled b j < nextWire (n+2) C)
    (rl : ∀i j,rel i j < nextWire (n+2) C)
    (ev : ∀(x : Input n) b j,value C (withConstants x) (enabled b j)=true ↔ E x b j)
    (rv : ∀(x : Input n) i j,value C (withConstants x) (rel i j)=true ↔ R x i j) :
    ∃ (D : Circuit) (out : Nat),FanInTwo D ∧ ReadsBack (n+2) D ∧
      K.circuit.gates <+: D.gates ∧ notCount D=notCount K.circuit ∧
      D.size ≤ K.circuit.size+7*m*m+N ∧ out < nextWire (n+2) D ∧
      ∀x : Input n,value D (withConstants x) out=true ↔
        Lib1436Subset.Collision (E x) (R x) ∨ ∃S,Lib1436Subset.DP (E x) (R x) S ∧ cut≤S.card := by
  classical
  let pairs : Fin (m*m) ≃ Fin m × Fin m := finProdFinEquiv.symm
  let rows : Fin (m*m) → List Nat := fun z=>
    let i := (pairs z).1
    let j := (pairs z).2
    [enabled true i,enabled false j,rel i i,rel i j,rel j i,rel j j]
  have er (b : Bool) (j : Fin m) := (el b j).trans_le (nextWire_le_of_prefix K.initial_prefix)
  have rr (i j : Fin m) := (rl i j).trans_le (nextWire_le_of_prefix K.initial_prefix)
  obtain ⟨A,term,af,ar,ap,an,az,al,av⟩ := append_and_rows K.circuit rows K.fan K.reads (by
    intro z a ha
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · exact er _ _
    · exact er _ _
    · exact rr _ _
    · exact rr _ _
    · exact rr _ _
    · exact rr _ _)
  have av' (x : Input n) z : value A (withConstants x) (term z)=true ↔
      E x true (pairs z).1 ∧ E x false (pairs z).2 ∧
      R x (pairs z).1 (pairs z).1 ∧ R x (pairs z).1 (pairs z).2 ∧
      R x (pairs z).2 (pairs z).1 ∧ R x (pairs z).2 (pairs z).2 := by
    have H := av x z
    simpa only [rows,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      keep K.initial_prefix (el _ _) x,keep K.initial_prefix (rl _ _) x,ev,rv] using H
  let big : Finset (Fin N) := Finset.univ.filter (fun z=>cut≤(e z).card)
  let row : Fin 1 → List Nat := fun _=>
    List.ofFn term ++ big.toList.map (fun z=>K.dp (e z))
  obtain ⟨D,out,df,dr,dp,dn,dz,dl,dv⟩ := append_or_rows A row af ar (by
    intro z a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
      exact al j
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
      exact (K.dp_live _).trans_le (nextWire_le_of_prefix ap))
  refine ⟨D,out 0,df,dr,ap.trans dp,dn.trans an,?_,dl 0,?_⟩
  · have hb : big.card≤N := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
    rw [dz,az]
    simp only [row,rows,List.length_append,List.length_ofFn,List.length_map,Finset.length_toList,
      List.length_cons,List.length_nil,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul]
    nlinarith
  · intro x
    rw [dv,collision_true_first]
    constructor
    · rintro ⟨a,ha,hv⟩
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨z,rfl⟩ := List.mem_ofFn.mp ha
        exact Or.inl ⟨(pairs z).1,(pairs z).2,(av' x z).mp hv⟩
      · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
        rw [keep ap (K.dp_live _) x,K.dp_value x _ (Finset.mem_univ _)] at hv
        exact Or.inr ⟨e z,hv,(Finset.mem_filter.mp (Finset.mem_toList.mp hz)).2⟩
    · rintro (⟨i,j,hi,hj,hii,hij,hji,hjj⟩ | ⟨S,hS,hc⟩)
      · refine ⟨term (pairs.symm (i,j)),List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨_,rfl⟩)),?_⟩
        apply (av' x _).mpr
        simpa using And.intro hi (And.intro hj (And.intro hii (And.intro hij (And.intro hji hjj))))
      · refine ⟨K.dp S,List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨e.symm S,?_,by simp⟩)),?_⟩
        · exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using hc⟩)
        · rw [keep ap (K.dp_live _) x,K.dp_value x _ (Finset.mem_univ _)]
          exact hS

end Lib1436Compile

namespace Lib1436Compile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

set_option maxHeartbeats 1200000 in
theorem append_threshold_bank {n m N q : Nat} {C : Circuit}
    {E : Input n → Bool → Fin m → Prop} {R : Input n → Fin m → Fin m → Prop}
    {F : Input n → Fin m → Prop}
    (K : Cache C E R F Finset.univ) (e : Fin N ≃ Finset (Fin m)) (ell : Fin q → Nat) :
    ∃ (D : Circuit) (out : Fin q → Nat),FanInTwo D ∧ ReadsBack (n+2) D ∧
      K.circuit.gates <+: D.gates ∧ notCount D=notCount K.circuit ∧
      D.size ≤ K.circuit.size+(q+2)*N ∧ (∀i,out i < nextWire (n+2) D) ∧
      ∀(x : Input n) i,value D (withConstants x) (out i)=true ↔
        ∃S,Lib1436Subset.DP (E x) (R x) S ∧ (∀j∈S,F x j) ∧ ell i≤S.card := by
  classical
  let terms : Fin N → List Nat := fun z=>[K.dp (e z),K.cap (e z)]
  obtain ⟨A,term,af,ar,ap,an,az,al,av⟩ := append_and_rows K.circuit terms K.fan K.reads (by
    intro z a ha
    simp only [terms,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact K.dp_live _
    · exact K.cap_live _)
  have av' (x : Input n) z : value A (withConstants x) (term z)=true ↔
      Lib1436Subset.DP (E x) (R x) (e z) ∧ ∀j∈e z,F x j := by
    have H := av x z
    simpa only [terms,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      K.dp_value x (e z) (Finset.mem_univ _),K.cap_value x (e z) (Finset.mem_univ _)] using H
  let eligible : Fin q → Finset (Fin N) := fun i=>Finset.univ.filter (fun z=>ell i≤(e z).card)
  let rows : Fin q → List Nat := fun i=>(eligible i).toList.map term
  obtain ⟨D,out,df,dr,dp,dn,dz,dl,dv⟩ := append_or_rows A rows af ar (by
    intro i a ha
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
    exact al z)
  refine ⟨D,out,df,dr,ap.trans dp,dn.trans an,?_,dl,?_⟩
  · have bound : ∑i,(rows i).length ≤ q*N := by
      calc
        ∑i,(rows i).length ≤ ∑_i : Fin q,N := by
          apply Finset.sum_le_sum
          intro i hi
          simp only [rows,List.length_map,Finset.length_toList]
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
        _ = q*N := by simp
    rw [dz,az]
    simp only [terms,List.length_cons,List.length_nil,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,Nat.nsmul_eq_mul,Nat.add_mul]
    omega
  · intro x i
    rw [dv]
    constructor
    · rintro ⟨a,ha,hv⟩
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
      have he : ell i≤(e z).card := (Finset.mem_filter.mp (Finset.mem_toList.mp hz)).2
      exact ⟨e z,((av' x z).mp hv).1,((av' x z).mp hv).2,he⟩
    · rintro ⟨S,hS,hF,he⟩
      refine ⟨term (e.symm S),List.mem_map.mpr ⟨e.symm S,?_,rfl⟩,?_⟩
      · apply Finset.mem_toList.mpr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using he⟩
      · apply (av' x (e.symm S)).mpr
        simpa using And.intro hS hF

end Lib1436Compile

namespace Lib1436Compile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

set_option maxHeartbeats 1600000 in
theorem programme_bank {n m q : Nat} (C : Circuit)
    (E : Input n → Bool → Fin m → Prop) (R : Input n → Fin m → Fin m → Prop)
    (F : Input n → Fin m → Prop) (cut : Nat) (ell : Fin q → Nat)
    (hf : FanInTwo C) (hr : ReadsBack (n+2) C)
    (enabled : Bool → Fin m → Nat) (rel : Fin m → Fin m → Nat) (capOne : Fin m → Nat)
    (el : ∀b j,enabled b j < nextWire (n+2) C)
    (rl : ∀i j,rel i j < nextWire (n+2) C)
    (fl : ∀i,capOne i < nextWire (n+2) C)
    (ev : ∀(x : Input n) b j,value C (withConstants x) (enabled b j)=true ↔ E x b j)
    (rv : ∀(x : Input n) i j,value C (withConstants x) (rel i j)=true ↔ R x i j)
    (fv : ∀(x : Input n) i,value C (withConstants x) (capOne i)=true ↔ F x i) :
    ∃ (D : Circuit) (decision : Nat) (threshold : Fin q → Nat),
      FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧ notCount D=notCount C ∧
      D.size≤C.size+(6*m+q+5)*2^m+7*m*m ∧
      decision < nextWire (n+2) D ∧ (∀i,threshold i < nextWire (n+2) D) ∧
      (∀x : Input n,value D (withConstants x) decision=true ↔
        Lib1436Subset.Collision (E x) (R x) ∨ ∃S,Lib1436Subset.DP (E x) (R x) S ∧ cut≤S.card) ∧
      (∀(x : Input n) i,value D (withConstants x) (threshold i)=true ↔
        ∃S,Lib1436Subset.DP (E x) (R x) S ∧ (∀j∈S,F x j) ∧ ell i≤S.card) := by
  classical
  obtain ⟨K⟩ := cache_all C E R F hf hr enabled rel capOne el rl fl ev rv fv
  obtain ⟨e,he⟩ := Lib1436Topology.enumeration m
  obtain ⟨A,decision,af,ar,ap,an,az,al,av⟩ :=
    append_failure_bank K e cut enabled rel el rl ev rv
  let KA := cache_lift K A af ar ap
  obtain ⟨D,threshold,df,dr,dp,dn,dz,dl,dv⟩ := append_threshold_bank KA e ell
  have cp : C.gates <+: D.gates := K.initial_prefix.trans (ap.trans dp)
  refine ⟨D,decision,threshold,df,dr,cp,dn.trans (an.trans K.nots),?_,
    al.trans_le (nextWire_le_of_prefix dp),dl,?_,dv⟩
  · have kz := K.size
    simp only [Finset.card_univ,Fintype.card_finset,Fintype.card_fin] at kz
    change D.size≤A.size+(q+2)*2^m at dz
    nlinarith
  · intro x
    rw [keep dp al x]
    exact av x

end Lib1436Compile

namespace Lib1436Compile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

theorem append_compat_cap {n m r : Nat} (C : Circuit)
    (Z O : Fin m → Fin r → Nat) (X : Fin r → Nat)
    (hf : FanInTwo C) (hr : ReadsBack (n+2) C)
    (zl : ∀ i v, Z i v < nextWire (n+2) C)
    (ol : ∀ i v, O i v < nextWire (n+2) C)
    (xl : ∀ v, X v < nextWire (n+2) C) :
    ∃ (D : Circuit) (rel : Fin m → Fin m → Nat) (cap : Fin m → Nat),
      FanInTwo D ∧ ReadsBack (n+2) D ∧ C.gates <+: D.gates ∧
      notCount D=notCount C ∧ D.size=C.size+2*m*m*r+2*m*r ∧
      (∀ i j, rel i j < nextWire (n+2) D) ∧
      (∀ i, cap i < nextWire (n+2) D) ∧
      (∀ (x : Input n) i j, value D (withConstants x) (rel i j)=true ↔
        ∀ v, value C (withConstants x) (Z i v)=true ∨
          value C (withConstants x) (O j v)=true) ∧
      (∀ (x : Input n) i, value D (withConstants x) (cap i)=true ↔
        ∀ v, value C (withConstants x) (Z i v)=true ∨
          value C (withConstants x) (X v)=true) := by
  classical
  let pair : Fin (m*m) → Fin m × Fin m := finProdFinEquiv.symm
  obtain ⟨A, rel, af, ar, ap, an, az, al, av⟩ := append_or_and_bank C
    (fun ij v => Z (pair ij).1 v) (fun ij v => O (pair ij).2 v) hf hr
    (fun ij v => zl _ _) (fun ij v => ol _ _)
  obtain ⟨D, cap, df, dr, dp, dn, dz, dl, dv⟩ := append_or_and_bank A Z
    (fun _ v => X v) af ar
    (fun i v => (zl i v).trans_le (nextWire_le_of_prefix ap))
    (fun _ v => (xl v).trans_le (nextWire_le_of_prefix ap))
  refine ⟨D, (fun i j => rel (finProdFinEquiv (i,j))), cap,
    df, dr, ap.trans dp, dn.trans an, ?_, ?_, dl, ?_, ?_⟩
  · rw [dz, az]
    ring
  · intro i j
    exact (al _).trans_le (nextWire_le_of_prefix dp)
  · intro x i j
    rw [keep dp (al _) x, av]
    simp only [pair, Equiv.symm_apply_apply]
  · intro x i
    rw [dv]
    simp only [keep ap (zl i _) x, keep ap (xl _) x]

end Lib1436Compile

namespace Lib1436Raw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

def t (m r : Nat) : Nat := 2*m*r+2*m

theorem flat_lt {m r : Nat} (i : Fin m) (v : Fin r) : i.val*r+v.val < m*r := by
  have hh := Nat.mul_le_mul_right r (Nat.succ_le_of_lt i.isLt)
  have hv := v.isLt
  nlinarith

def z {m r extra : Nat} (i : Fin m) (v : Fin r) : Fin (t m r+extra) :=
  ⟨i.val*r+v.val, by have hh := flat_lt i v; simp only [t, Nat.mul_assoc]; omega⟩

def o {m r extra : Nat} (i : Fin m) (v : Fin r) : Fin (t m r+extra) :=
  ⟨m*r+i.val*r+v.val, by have hh := flat_lt i v; simp only [t, Nat.mul_assoc]; omega⟩

def en {m r extra : Nat} (b : Bool) (i : Fin m) : Fin (t m r+extra) :=
  ⟨2*m*r+(if b then m else 0)+i.val, by
    have hi := i.isLt
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true]
    all_goals unfold t; omega⟩

def query {m r : Nat} (v : Fin r) : Fin (t m r+r) :=
  ⟨t m r+v.val, by have hv := v.isLt; omega⟩

def decodeZ {m r extra : Nat} (x : Input (t m r+extra)) (i : Fin m) : Finset Nat :=
  (Finset.univ.filter (fun v : Fin r => x (z i v)=true)).image Fin.val

def decodeO {m r extra : Nat} (x : Input (t m r+extra)) (i : Fin m) : Finset Nat :=
  (Finset.univ.filter (fun v : Fin r => x (o i v)=true)).image Fin.val

def decodeE {m r extra : Nat} (x : Input (t m r+extra)) (b : Bool) : Finset Nat :=
  (Finset.univ.filter (fun i : Fin m => x (en b i)=true)).image Fin.val

def decodeX {m r : Nat} (x : Input (t m r+r)) : Finset Nat :=
  (Finset.univ.filter (fun v : Fin r => x (query v)=true)).image Fin.val

theorem decodeZ_mem {m r extra : Nat} (x : Input (t m r+extra)) (i : Fin m) (v : Fin r) :
    v.val ∈ decodeZ x i ↔ x (z i v)=true := by
  simp only [decodeZ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hav⟩
    have he : a = v := Fin.ext hav
    simpa only [he] using ha
  · intro hh
    exact ⟨v, hh, rfl⟩

theorem decodeO_mem {m r extra : Nat} (x : Input (t m r+extra)) (i : Fin m) (v : Fin r) :
    v.val ∈ decodeO x i ↔ x (o i v)=true := by
  simp only [decodeO, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hav⟩
    have he : a = v := Fin.ext hav
    simpa only [he] using ha
  · intro hh
    exact ⟨v, hh, rfl⟩

theorem decodeE_mem {m r extra : Nat} (x : Input (t m r+extra)) (b : Bool) (i : Fin m) :
    i.val ∈ decodeE x b ↔ x (en b i)=true := by
  simp only [decodeE, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hav⟩
    have he : a = i := Fin.ext hav
    simpa only [he] using ha
  · intro hh
    exact ⟨i, hh, rfl⟩

theorem decodeX_mem {m r : Nat} (x : Input (t m r+r)) (v : Fin r) :
    v.val ∈ decodeX x ↔ x (query v)=true := by
  simp only [decodeX, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hav⟩
    have he : a = v := Fin.ext hav
    simpa only [he] using ha
  · intro hh
    exact ⟨v, hh, rfl⟩

theorem decodeZ_bound {m r extra : Nat} (x : Input (t m r+extra)) (i : Fin m) :
    decodeZ x i ⊆ Finset.range r := by
  intro v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_range.mpr a.isLt

theorem decodeO_bound {m r extra : Nat} (x : Input (t m r+extra)) (i : Fin m) :
    decodeO x i ⊆ Finset.range r := by
  intro v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_range.mpr a.isLt

theorem decodeE_bound {m r extra : Nat} (x : Input (t m r+extra)) (b : Bool) :
    decodeE x b ⊆ Finset.range m := by
  intro i hi
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_range.mpr a.isLt

theorem decodeX_bound {m r : Nat} (x : Input (t m r+r)) :
    decodeX x ⊆ Finset.range r := by
  intro v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_range.mpr a.isLt

theorem relation_iff {m r extra : Nat} (x : Input (t m r+extra)) (i j : Fin m) :
    (∀ v, x (z i v)=true ∨ x (o j v)=true) ↔
      Finset.range r \ decodeZ x i ⊆ decodeO x j := by
  constructor
  · intro h v hv
    obtain ⟨hr, hz⟩ := Finset.mem_sdiff.mp hv
    let a : Fin r := ⟨v, Finset.mem_range.mp hr⟩
    have hza : x (z i a) ≠ true := by
      intro hh
      exact hz ((decodeZ_mem x i a).mpr hh)
    exact (decodeO_mem x j a).mpr ((h a).resolve_left hza)
  · intro h v
    by_cases hz : x (z i v)=true
    · exact Or.inl hz
    · right
      apply (decodeO_mem x j v).mp
      apply h
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr v.isLt,
        fun hh => hz ((decodeZ_mem x i v).mp hh)⟩

theorem cap_iff {m r : Nat} (x : Input (t m r+r)) (i : Fin m) :
    (∀ v, x (z i v)=true ∨ x (query v)=true) ↔
      Finset.range r \ decodeZ x i ⊆ decodeX x := by
  constructor
  · intro h v hv
    obtain ⟨hr, hz⟩ := Finset.mem_sdiff.mp hv
    let a : Fin r := ⟨v, Finset.mem_range.mp hr⟩
    have hza : x (z i a) ≠ true := by
      intro hh
      exact hz ((decodeZ_mem x i a).mpr hh)
    exact (decodeX_mem x a).mpr ((h a).resolve_left hza)
  · intro h v
    by_cases hz : x (z i v)=true
    · exact Or.inl hz
    · right
      apply (decodeX_mem x v).mp
      apply h
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr v.isLt,
        fun hh => hz ((decodeZ_mem x i v).mp hh)⟩

end Lib1436Raw

namespace Lib1436Raw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

theorem raw_bank (m r : Nat) :
    ∃ (C : Circuit) (rel : Fin m → Fin m → Nat) (cap : Fin m → Nat),
      FanInTwo C ∧ ReadsBack (t m r+r+2) C ∧ notCount C=0 ∧
      C.size=2*m*m*r+2*m*r ∧
      (∀ (b : Bool) (i : Fin m), (en (m:=m) (r:=r) (extra:=r) b i).val < nextWire (t m r+r+2) C) ∧
      (∀ i j, rel i j < nextWire (t m r+r+2) C) ∧
      (∀ i, cap i < nextWire (t m r+r+2) C) ∧
      (∀ (x : Input (t m r+r)) (b : Bool) (i : Fin m),
        value C (withConstants x) (en (m:=m) (r:=r) (extra:=r) b i).val=true ↔ i.val ∈ decodeE x b) ∧
      (∀ (x : Input (t m r+r)) i j,
        value C (withConstants x) (rel i j)=true ↔
          Finset.range r \ decodeZ x i ⊆ decodeO x j) ∧
      (∀ (x : Input (t m r+r)) i,
        value C (withConstants x) (cap i)=true ↔
          Finset.range r \ decodeZ x i ⊆ decodeX x) := by
  classical
  have raw_live (v : Fin (t m r+r)) : v.val < nextWire (t m r+r+2) emptyCircuit := by
    have hv := v.isLt
    simp only [nextWire, emptyCircuit, Circuit.size, List.length_nil]
    omega
  obtain ⟨C, rel, cap, cf, cr, cp, cn, cs, rl, fl, rv, fv⟩ :=
    Lib1436Compile.append_compat_cap (n:=t m r+r) (m:=m) (r:=r) emptyCircuit
      (fun i v => (z (extra:=r) i v).val)
      (fun i v => (o (extra:=r) i v).val) (fun v => (query (m:=m) v).val)
      emptyCircuit_fanInTwo (emptyCircuit_readsBack _)
      (fun i v => raw_live (z i v)) (fun i v => raw_live (o i v))
      (fun v => raw_live (query v))
  refine ⟨C, rel, cap, cf, cr, cn.trans emptyCircuit_notCount, ?_, ?_, rl, fl, ?_, ?_, ?_⟩
  · simpa only [emptyCircuit, Circuit.size, List.length_nil, Nat.zero_add] using cs
  · intro b i
    exact (raw_live (en b i)).trans_le (nextWire_le_of_prefix cp)
  · intro x b i
    rw [input_value]
    exact (decodeE_mem x b i).symm
  · intro x i j
    have hh : value C (withConstants x) (rel i j)=true ↔
        ∀ v, x (z i v)=true ∨ x (o j v)=true := by
      simpa only [input_value] using rv x i j
    exact hh.trans (relation_iff x i j)
  · intro x i
    have hh : value C (withConstants x) (cap i)=true ↔
        ∀ v, x (z i v)=true ∨ x (query v)=true := by
      simpa only [input_value] using fv x i
    exact hh.trans (cap_iff x i)

end Lib1436Raw

namespace Lib1436Raw
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base

def decodeZFin {m r extra : Nat} (x : Input (t m r+extra)) (i : Fin m) : Finset (Fin r) :=
  Finset.univ.filter (fun v => x (z i v)=true)

def decodeOFin {m r extra : Nat} (x : Input (t m r+extra)) (i : Fin m) : Finset (Fin r) :=
  Finset.univ.filter (fun v => x (o i v)=true)

def decodeEFin {m r extra : Nat} (x : Input (t m r+extra)) (b : Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => x (en b i)=true)

def decodeXFin {m r : Nat} (x : Input (t m r+r)) : Finset (Fin r) :=
  Finset.univ.filter (fun v => x (query v)=true)

theorem relationFin_iff {m r extra : Nat} (x : Input (t m r+extra)) (i j : Fin m) :
    (∀ v, x (z i v)=true ∨ x (o j v)=true) ↔
      (decodeZFin x i)ᶜ ⊆ decodeOFin x j := by
  constructor
  · intro h v hv
    have hz : x (z i v) ≠ true := by simpa [decodeZFin] using hv
    simpa [decodeOFin] using (h v).resolve_left hz
  · intro h v
    by_cases hz : x (z i v)=true
    · exact Or.inl hz
    · right
      have hv : v ∈ (decodeZFin x i)ᶜ := by simpa [decodeZFin] using hz
      simpa [decodeOFin] using h hv

theorem capFin_iff {m r : Nat} (x : Input (t m r+r)) (i : Fin m) :
    (∀ v, x (z i v)=true ∨ x (query v)=true) ↔
      (decodeZFin x i)ᶜ ⊆ decodeXFin x := by
  constructor
  · intro h v hv
    have hz : x (z i v) ≠ true := by simpa [decodeZFin] using hv
    simpa [decodeXFin] using (h v).resolve_left hz
  · intro h v
    by_cases hz : x (z i v)=true
    · exact Or.inl hz
    · right
      have hv : v ∈ (decodeZFin x i)ᶜ := by simpa [decodeZFin] using hz
      simpa [decodeXFin] using h hv

theorem raw_bank_fin (m r : Nat) :
    ∃ (C : Circuit) (rel : Fin m → Fin m → Nat) (cap : Fin m → Nat),
      FanInTwo C ∧ ReadsBack (t m r+r+2) C ∧ notCount C=0 ∧
      C.size=2*m*m*r+2*m*r ∧
      (∀ (b : Bool) (i : Fin m), (en (m:=m) (r:=r) (extra:=r) b i).val < nextWire (t m r+r+2) C) ∧
      (∀ i j, rel i j < nextWire (t m r+r+2) C) ∧
      (∀ i, cap i < nextWire (t m r+r+2) C) ∧
      (∀ (x : Input (t m r+r)) (b : Bool) (i : Fin m),
        value C (withConstants x) (en (m:=m) (r:=r) (extra:=r) b i).val=true ↔ i ∈ decodeEFin x b) ∧
      (∀ (x : Input (t m r+r)) i j,
        value C (withConstants x) (rel i j)=true ↔
          (decodeZFin x i)ᶜ ⊆ decodeOFin x j) ∧
      (∀ (x : Input (t m r+r)) i,
        value C (withConstants x) (cap i)=true ↔
          (decodeZFin x i)ᶜ ⊆ decodeXFin x) := by
  obtain ⟨C,rel,cap,hf,hr,hn,hs,el,rl,fl,ev,rv,fv⟩ := raw_bank m r
  refine ⟨C,rel,cap,hf,hr,hn,hs,el,rl,fl,?_,?_,?_⟩
  · intro x b i
    rw [input_value]
    simp [decodeEFin]
  · intro x i j
    exact (rv x i j).trans ((relation_iff x i j).symm.trans (relationFin_iff x i j))
  · intro x i
    exact (fv x i).trans ((cap_iff x i).symm.trans (capFin_iff x i))

end Lib1436Raw

namespace Lib1436Raw
open Base

def join {m r : Nat} (x : Input (t m r)) (y : Input r) : Input (t m r+r) :=
  Fin.append x y

theorem join_z {m r : Nat} (x : Input (t m r)) (y : Input r) (i : Fin m) (v : Fin r) :
    join x y (z i v) = x (z (extra:=0) i v) := by
  have hh : z (extra:=r) i v = Fin.castAdd r (z (extra:=0) i v) := Fin.ext rfl
  rw [hh]
  exact Fin.append_left x y _

theorem join_o {m r : Nat} (x : Input (t m r)) (y : Input r) (i : Fin m) (v : Fin r) :
    join x y (o i v) = x (o (extra:=0) i v) := by
  have hh : o (extra:=r) i v = Fin.castAdd r (o (extra:=0) i v) := Fin.ext rfl
  rw [hh]
  exact Fin.append_left x y _

theorem join_en {m r : Nat} (x : Input (t m r)) (y : Input r) (b : Bool) (i : Fin m) :
    join x y (en b i) = x (en (r:=r) (extra:=0) b i) := by
  have hh : en (r:=r) (extra:=r) b i = Fin.castAdd r (en (r:=r) (extra:=0) b i) := Fin.ext rfl
  rw [hh]
  exact Fin.append_left x y _

theorem join_query {m r : Nat} (x : Input (t m r)) (y : Input r) (v : Fin r) :
    join x y (query v) = y v := by
  have hh : query (m:=m) v = Fin.natAdd (t m r) v := Fin.ext rfl
  rw [hh]
  exact Fin.append_right x y v

theorem withConstants_join {m r : Nat} (x : Input (t m r)) (y : Input r) :
    withConstants (join x y) = List.ofFn x ++ withConstants y := by
  simp only [withConstants, join, List.ofFn_fin_append, List.append_assoc]

theorem decodeZFin_join {m r : Nat} (x : Input (t m r)) (y y' : Input r) :
    decodeZFin (join x y) = decodeZFin (join x y') := by
  funext i
  ext v
  simp only [decodeZFin, Finset.mem_filter, Finset.mem_univ, true_and, join_z]

theorem decodeOFin_join {m r : Nat} (x : Input (t m r)) (y y' : Input r) :
    decodeOFin (join x y) = decodeOFin (join x y') := by
  funext i
  ext v
  simp only [decodeOFin, Finset.mem_filter, Finset.mem_univ, true_and, join_o]

theorem decodeEFin_join {m r : Nat} (x : Input (t m r)) (y y' : Input r) :
    decodeEFin (join x y) = decodeEFin (join x y') := by
  funext b
  ext i
  simp only [decodeEFin, Finset.mem_filter, Finset.mem_univ, true_and, join_en]

noncomputable def table {m r : Nat} (A : Fin m → Finset Nat) : Fin (m*r) → Bool := by
  classical
  exact fun k => decide (((finProdFinEquiv : Fin m × Fin r ≃ Fin (m*r)).symm k).2.val ∈
    A (((finProdFinEquiv : Fin m × Fin r ≃ Fin (m*r)).symm k).1))

theorem table_flat {m r : Nat} (A : Fin m → Finset Nat) (i : Fin m) (v : Fin r) :
    table A ⟨i.val*r+v.val, flat_lt i v⟩ = decide (v.val ∈ A i) := by
  classical
  have hh : (⟨i.val*r+v.val, flat_lt i v⟩ : Fin (m*r)) = finProdFinEquiv (i,v) := by
    apply Fin.ext
    change i.val*r+v.val = v.val+r*i.val
    ring
  rw [hh]
  simp only [table, Equiv.symm_apply_apply]

theorem table_list {m r : Nat} (A : Fin m → Finset Nat) :
    List.ofFn (table (r:=r) A) =
      (List.ofFn (fun i : Fin m => List.ofFn (fun v : Fin r => decide (v.val ∈ A i)))).flatten := by
  classical
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext v
  exact table_flat A i v

noncomputable def raw {m r : Nat} (Z O : Fin m → Finset Nat) (E : Bool → Finset Nat) : List Bool := by
  classical
  exact List.ofFn (table (r:=r) Z) ++ (List.ofFn (table (r:=r) O) ++
    (List.ofFn (fun i : Fin m => decide (i.val ∈ E false)) ++
      List.ofFn (fun i : Fin m => decide (i.val ∈ E true))))

theorem raw_length {m r : Nat} (Z O : Fin m → Finset Nat) (E : Bool → Finset Nat) :
    (raw (r:=r) Z O E).length = t m r := by
  simp only [raw, List.length_append, List.length_ofFn, t]
  ring

noncomputable def encode {m r : Nat} (Z O : Fin m → Finset Nat) (E : Bool → Finset Nat) : Input (t m r) :=
  fun i => (raw (r:=r) Z O E).getD i.val false

theorem ofFn_encode_raw {m r : Nat} (Z O : Fin m → Finset Nat) (E : Bool → Finset Nat) :
    List.ofFn (encode (r:=r) Z O E) = raw (r:=r) Z O E := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, raw_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, encode, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj, Option.getD_some]

theorem ofFn_encode {m r : Nat} (Z O : Fin m → Finset Nat) (E : Bool → Finset Nat) :
    List.ofFn (encode (r:=r) Z O E) =
      (List.ofFn (fun i : Fin m => List.ofFn (fun v : Fin r => decide (v.val ∈ Z i)))).flatten ++
      (List.ofFn (fun i : Fin m => List.ofFn (fun v : Fin r => decide (v.val ∈ O i)))).flatten ++
      List.ofFn (fun i : Fin m => decide (i.val ∈ E false)) ++
      List.ofFn (fun i : Fin m => decide (i.val ∈ E true)) := by
  rw [ofFn_encode_raw]
  simp only [raw, table_list, List.append_assoc]

private theorem getD_ofFn {N : Nat} (f : Fin N → Bool) (i : Fin N) :
    (List.ofFn f).getD i.val false = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]

theorem encode_z {m r : Nat} (Z O : Fin m → Finset Nat) (E : Bool → Finset Nat)
    (i : Fin m) (v : Fin r) :
    encode Z O E (z (extra:=0) i v) = decide (v.val ∈ Z i) := by
  classical
  change (raw (r:=r) Z O E).getD (i.val*r+v.val) false = _
  rw [raw, List.getD_append _ _ _ _ (by simpa using flat_lt i v)]
  exact (getD_ofFn (table Z) ⟨_, flat_lt i v⟩).trans (table_flat Z i v)

theorem encode_o {m r : Nat} (Z O : Fin m → Finset Nat) (E : Bool → Finset Nat)
    (i : Fin m) (v : Fin r) :
    encode Z O E (o (extra:=0) i v) = decide (v.val ∈ O i) := by
  classical
  change (raw (r:=r) Z O E).getD (m*r+i.val*r+v.val) false = _
  rw [raw, List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn]
  have hh : m*r+i.val*r+v.val-m*r = i.val*r+v.val := by omega
  rw [hh, List.getD_append _ _ _ _ (by simpa using flat_lt i v)]
  exact (getD_ofFn (table O) ⟨_, flat_lt i v⟩).trans (table_flat O i v)

theorem encode_en {m r : Nat} (Z O : Fin m → Finset Nat) (E : Bool → Finset Nat)
    (b : Bool) (i : Fin m) :
    encode (r:=r) Z O E (en (r:=r) (extra:=0) b i) = decide (i.val ∈ E b) := by
  classical
  change (raw (r:=r) Z O E).getD (2*m*r+(if b then m else 0)+i.val) false = _
  have hm : 2*m*r = m*r+m*r := by ring
  have hz : m*r ≤ 2*m*r+(if b then m else 0)+i.val := by omega
  rw [raw, List.getD_append_right _ _ _ _ (by simpa using hz)]
  simp only [List.length_ofFn]
  have hh : 2*m*r+(if b then m else 0)+i.val-m*r = m*r+(if b then m else 0)+i.val := by omega
  rw [hh, List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn]
  have hh' : m*r+(if b then m else 0)+i.val-m*r = (if b then m else 0)+i.val := by omega
  rw [hh']
  cases b with
  | false =>
      simp only [Bool.false_eq_true, if_false, Nat.zero_add]
      rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
      exact getD_ofFn _ i
  | true =>
      simp only [if_true]
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left]
      exact getD_ofFn _ i

theorem decode_encode {m r : Nat} (Z O : Fin m → Finset Nat) (E : Bool → Finset Nat)
    (y : Input r) :
    (∀ i, decodeZFin (join (encode Z O E) y) i = Finset.univ.filter (fun v : Fin r => v.val ∈ Z i)) ∧
    (∀ i, decodeOFin (join (encode Z O E) y) i = Finset.univ.filter (fun v : Fin r => v.val ∈ O i)) ∧
    (∀ b, decodeEFin (join (encode Z O E) y) b = Finset.univ.filter (fun i : Fin m => i.val ∈ E b)) ∧
    decodeXFin (join (encode Z O E) y) = Finset.univ.filter (fun v => y v=true) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    ext v
    simp [decodeZFin, join_z, encode_z]
  · intro i
    ext v
    simp [decodeOFin, join_o, encode_o]
  · intro b
    ext i
    simp [decodeEFin, join_en, encode_en]
  · ext v
    simp [decodeXFin, join_query]

end Lib1436Raw

namespace Lib1436Compiled
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket Base Lib1436Raw

def Enabled {m r extra : Nat} (x : Input (t m r+extra)) (b : Bool) (i : Fin m) : Prop :=
  i∈decodeEFin x b

def Lower {m r extra : Nat} (x : Input (t m r+extra)) (i : Fin m) : Finset (Fin r) :=
  (decodeZFin x i)ᶜ

def Upper {m r extra : Nat} (x : Input (t m r+extra)) (i : Fin m) : Finset (Fin r) :=
  decodeOFin x i

theorem compiled (m r b : Nat) :
    ∃ (D : Circuit) (decision : Nat) (threshold : Fin (m+2) → Nat),
      FanInTwo D ∧ ReadsBack (t m r+r+2) D ∧ notCount D=0 ∧
      D.size≤2*m*m*r+2*m*r+(7*m+7)*2^m+7*m*m ∧
      decision < nextWire (t m r+r+2) D ∧
      (∀i,threshold i < nextWire (t m r+r+2) D) ∧
      (∀x : Input (t m r+r),value D (withConstants x) decision=true ↔
        Lib1436Subset.Collision (Enabled x) (fun i j=>Lower x i⊆Upper x j) ∨
        ∃S,Lib1436Subset.DP (Enabled x) (fun i j=>Lower x i⊆Upper x j) S ∧ 2*2^b≤S.card) ∧
      (∀(x : Input (t m r+r)) (ell : Fin (m+2)),value D (withConstants x) (threshold ell)=true ↔
        ∃S,Lib1436Subset.DP (Enabled x) (fun i j=>Lower x i⊆Upper x j) S ∧
          (∀j∈S,Lower x j⊆decodeXFin x) ∧ ell.val≤S.card) := by
  obtain ⟨C,rel,cap,cf,cr,cn,cs,el,rl,fl,ev,rv,fv⟩ := raw_bank_fin m r
  obtain ⟨D,decision,threshold,df,dr,dp,dn,dz,dl,tl,dv,tv⟩ :=
    Lib1436Compile.programme_bank C
      (fun x b i=>i∈decodeEFin x b)
      (fun x i j=>(decodeZFin x i)ᶜ⊆decodeOFin x j)
      (fun x i=>(decodeZFin x i)ᶜ⊆decodeXFin x)
      (2*2^b) (fun ell : Fin (m+2)=>ell.val) cf cr
      (fun b i=>(en (m:=m) (r:=r) (extra:=r) b i).val) rel cap el rl fl ev rv fv
  refine ⟨D,decision,threshold,df,dr,dn.trans cn,?_,dl,tl,dv,tv⟩
  rw [cs] at dz
  convert dz using 1 <;> ring

end Lib1436Compiled

namespace Lib1436Readout
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Base

theorem append {n d b : Nat} (A : Circuit) (odd : Fin (d+1) → Nat) (even : Fin d → Nat)
    (hf : FanInTwo A) (hr : ReadsBack (n+2) A) (hn : notCount A=0)
    (ho : ∀i,odd i < nextWire (n+2) A) (he : ∀i,even i < nextWire (n+2) A)
    (hb : d < 2^b) (hord : ∀x : Input n,Antitone (fun i=>value A (withConstants x) (even i))) :
    ∃(C : Circuit)(out : Nat),FanInTwo C ∧ ReadsBack (n+2) C ∧ A.gates <+: C.gates ∧
      notCount C ≤ b ∧ C.size-notCount C ≤ A.size+7*d+1 ∧ out < nextWire (n+2) C ∧
      ∀x : Input n,value C (withConstants x) out=true ↔
        value A (withConstants x) (odd (Fin.last d))=true ∨
          ∃q : Fin d,value A (withConstants x) (odd q.castSucc)=true ∧ value A (withConstants x) (even q)=false := by
  classical
  obtain ⟨I⟩ := invert_taps withConstants withConstants_length hb hf hr n
    (by unfold nextWire;omega) (false_value A) even he hord
  let rows : Fin d → List Nat := fun q=>[odd q.castSucc,I.wires q]
  have rowsLive : ∀q a,a∈rows q → a < nextWire (n+2) I.circuit := by
    intro q a ha
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl
    · exact (ho _).trans_le (nextWire_le_of_prefix I.extension)
    · exact I.valid q
  obtain ⟨B,p,bf,br,bext,bn,bs,bv,bsem⟩ :=
    Lib1436Compile.append_and_rows I.circuit rows I.fanInTwo I.readsBack rowsLive
  have bs' : B.size=I.circuit.size+2*d := by simpa [rows,Nat.mul_comm] using bs
  let orows : Fin 1 → List Nat := fun _=>odd (Fin.last d)::List.ofFn p
  have orowsLive : ∀i a,a∈orows i → a < nextWire (n+2) B := by
    intro i a ha
    simp only [orows,List.mem_cons,List.mem_ofFn] at ha
    rcases ha with rfl | ⟨q,rfl⟩
    · exact (ho _).trans_le (nextWire_le_of_prefix (I.extension.trans bext))
    · exact bv q
  obtain ⟨C,o,cf,cr,cext,cn,cs,cv,csem⟩ := append_or_rows B orows bf br orowsLive
  have cs' : C.size=B.size+(d+1) := by simpa [orows] using cs
  have cnot : notCount C=I.inversions := by rw [cn,bn,I.count_eq,hn,Nat.zero_add]
  have hpref : A.gates <+: C.gates := I.extension.trans (bext.trans cext)
  refine ⟨C,o 0,cf,cr,hpref,?_,?_,cv 0,?_⟩
  · rw [cnot]
    exact I.inversionsBound
  · have hsz := I.size_eq
    have hbin := I.binaryBound
    rw [cnot]
    omega
  · intro x
    have hp (q : Fin d) : value B (withConstants x) (p q)=true ↔
        value A (withConstants x) (odd q.castSucc)=true ∧ value A (withConstants x) (even q)=false := by
      rw [bsem]
      simp only [rows,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
      rw [value_of_prefix I.extension (by simpa only [withConstants_length] using ho q.castSucc),I.computes]
      simp only [Bool.not_eq_true_eq_eq_false]
    have hlast : value B (withConstants x) (odd (Fin.last d))=value A (withConstants x) (odd (Fin.last d)) :=
      value_of_prefix (I.extension.trans bext) (by simpa only [withConstants_length] using ho (Fin.last d))
    rw [csem]
    simp only [orows,List.mem_cons,List.mem_ofFn]
    constructor
    · rintro ⟨a,(ha | ⟨q,hq⟩),hv⟩
      · subst a
        exact Or.inl (hlast ▸ hv)
      · subst a
        exact Or.inr ⟨q,(hp q).mp hv⟩
    · rintro (hv | ⟨q,hq⟩)
      · exact ⟨odd (Fin.last d),Or.inl rfl,hlast.symm ▸ hv⟩
      · exact ⟨p q,Or.inr ⟨q,rfl⟩,(hp q).mpr hq⟩

end Lib1436Readout

namespace Lib1436Decoder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Base

theorem append {n m r b : Nat} (A : Circuit) (threshold : Fin (m+2) → Nat)
    (E : Input n → Bool → Fin m → Prop)
    (lo hi : Input n → Fin m → Finset (Fin r)) (X : Input n → Finset (Fin r))
    (hf : FanInTwo A) (hr : ReadsBack (n+2) A) (hn : notCount A=0)
    (ht : ∀i,threshold i < nextWire (n+2) A)
    (hv : ∀x i,value A (withConstants x) (threshold i)=true ↔
      Lib1436Threshold.T (E x) (lo x) (hi x) i.val (X x)) :
    ∃(C : Circuit)(out : Nat),FanInTwo C ∧ ReadsBack (n+2) C ∧ A.gates <+: C.gates ∧
      notCount C≤b ∧ C.size-notCount C≤A.size+7*m+1 ∧ out < nextWire (n+2) C ∧
      ∀x,Lib1436Criterion.ScalarFits (E x) (lo x) (hi x) b →
        ∀j v,E x v j → Lib1436Boxes.Box (lo x) (hi x) j (X x) →
          value C (withConstants x) out=v := by
  classical
  let d := Lib1436Threshold.depthCap m b
  have hd : d≤m/2 := Nat.min_le_left _ _
  have hdm : d≤m := hd.trans (Nat.div_le_self _ _)
  let oi : Fin (d+1) → Fin (m+2) := fun q=>⟨2*q.val+1,by have hh:=q.isLt;omega⟩
  let ei : Fin d → Fin (m+2) := fun q=>⟨2*q.val+2,by have hh:=q.isLt;omega⟩
  have hord : ∀x : Input n,Antitone (fun q : Fin d=>value A (withConstants x) (threshold (ei q))) := by
    intro x i j hij
    apply Bool.le_iff_imp.mpr
    intro hj
    apply (hv x (ei i)).mpr
    apply Lib1436Threshold.antitone (E x) (lo x) (hi x) (X x) (by
      have hh := Fin.le_def.mp hij
      change 2*i.val+2≤2*j.val+2
      omega)
    exact (hv x (ei j)).mp hj
  obtain ⟨C,out,cf,cr,cp,cn,cs,co,cv⟩ := Lib1436Readout.append A
    (fun q=>threshold (oi q)) (fun q=>threshold (ei q)) hf hr hn
    (fun q=>ht (oi q)) (fun q=>ht (ei q)) (Lib1436Threshold.depthCap_lt m b) hord
  refine ⟨C,out,cf,cr,cp,cn,by omega,co,?_⟩
  intro x hfit j v he hbox
  have hh := (Lib1436Criterion.scalar_iff (E x) (lo x) (hi x) b).mp hfit
  have hnoc : ¬Lib1436Subset.Collision (E x) (fun i j=>lo x i⊆hi x j) :=
    fun hc=>hh.1 ((Lib1436Boxes.collision_iff_bad (E x) (lo x) (hi x)).mp hc)
  have hend := Lib1436Threshold.terminal b hh.2 (X x)
  have hread : value C (withConstants x) out=true ↔
      Lib1436Threshold.Read (E x) (lo x) (hi x) d (X x) := by
    rw [cv]
    simp only [Bool.eq_false_iff,hv,oi,ei,Fin.val_last,Fin.val_castSucc,Lib1436Threshold.Read]
    simp only [ne_eq,hv]
  have hbool : value C (withConstants x) out=true ↔ v=true :=
    hread.trans (Lib1436Threshold.read_correct d (X x) hnoc hend j v he hbox)
  cases hval : value C (withConstants x) out <;> cases v <;> simp_all

end Lib1436Decoder


namespace Lib1218Relabel

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma circuit_wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (wiresFrom gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    · exact getD_append_left _ _ k false hk
    · simp; omega

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    have h1 : gs.take j ++ gs.drop j = gs := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1.symm
  conv_lhs => rw [hsplit]
  rw [wiresFrom_append, wiresFrom_cons]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (le_of_lt hj)]
  rw [wiresFrom_getD_lt _ _ (w.length + j) (by simp [hlen])]
  rw [getD_append_right _ _ (w.length + j) false (by omega)]
  simp [hlen]

lemma wiresFrom_getD_gate_readsBack (gs : List Gate) (w : List Bool)
    (hrb : ReadsBack w.length ⟨gs, 0⟩) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresFrom gs w).getD i false) := by
  rw [wiresFrom_getD_gate gs w j hj]
  congr 1
  refine List.map_congr_left (fun i hi => ?_)
  have hi_lt : i < w.length + j := by
    have h := hrb j hj
    rw [gateAt_eq_getElem _ j hj] at h
    exact h i hi
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  conv_rhs => rw [hsplit, wiresFrom_append]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (le_of_lt hj)]
  symm
  exact wiresFrom_getD_lt (gs.drop j) (wiresFrom (gs.take j) w) i (by omega)

lemma fanInTwo_map_inputs {gs : List Gate} {φ : ℕ → ℕ} {o : ℕ}
    (h : FanInTwo ⟨gs, 0⟩) :
    FanInTwo ⟨gs.map (fun g => ⟨g.op, g.inputs.map φ⟩), o⟩ := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
  have h0 := h g0 hg0
  exact ⟨h0.1, by simpa using h0.2⟩

lemma wiresFrom_remap_full (gs : List Gate) (w1 W0 : List Bool) (φ : ℕ → ℕ)
    (hrb : ReadsBack w1.length ⟨gs, 0⟩)
    (hφ_lt : ∀ k < w1.length, φ k < W0.length)
    (hφ_gate : ∀ j < gs.length, φ (w1.length + j) = W0.length + j)
    (hφ_val : ∀ k < w1.length, W0.getD (φ k) false = w1.getD k false) :
    let gs' := gs.map (fun g => ⟨g.op, g.inputs.map φ⟩)
    ReadsBack W0.length ⟨gs', 0⟩ ∧
    ∀ t < w1.length + gs.length,
      (wiresFrom gs' W0).getD (φ t) false = (wiresFrom gs w1).getD t false := by
  intro gs'
  have hrb' : ReadsBack W0.length ⟨gs', 0⟩ := by
    intro j hj i hi
    have hj0 : j < gs.length := by simpa [gs'] using hj
    rw [gateAt_eq_getElem _ j hj] at hi
    simp only [gs', List.getElem_map, List.mem_map] at hi
    rcases hi with ⟨k, hk, rfl⟩
    have hk_lt : k < w1.length + j := by
      have h := hrb j hj0
      rw [gateAt_eq_getElem _ j hj0] at h
      exact h k hk
    by_cases hkw : k < w1.length
    · exact lt_of_lt_of_le (hφ_lt k hkw) (Nat.le_add_right _ _)
    · have hj' : k - w1.length < gs.length := by omega
      have hkeq : k = w1.length + (k - w1.length) := by omega
      rw [hkeq, hφ_gate (k - w1.length) hj']
      omega
  refine ⟨hrb', ?_⟩
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht
    by_cases htw : t < w1.length
    · rw [wiresFrom_getD_lt gs' W0 (φ t) (hφ_lt t htw)]
      rw [wiresFrom_getD_lt gs w1 t htw]
      exact hφ_val t htw
    · let j := t - w1.length
      have hj : j < gs.length := by omega
      have hteq : t = w1.length + j := by omega
      rw [hteq, hφ_gate j hj]
      have hj' : j < gs'.length := by simpa [gs'] using hj
      rw [wiresFrom_getD_gate_readsBack gs' W0 hrb' j hj']
      rw [wiresFrom_getD_gate_readsBack gs w1 hrb j hj]
      simp only [gs', List.getElem_map, List.map_map]
      congr 1
      refine List.map_congr_left (fun k hk => ?_)
      have hk_lt : k < w1.length + j := by
        have h := hrb j hj
        rw [gateAt_eq_getElem _ j hj] at h
        exact h k hk
      exact ih k (by omega) (by omega)

def inputs {n : Nat} (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ [false, true]

@[simp] theorem inputs_length {n : Nat} (x : Fin n → Bool) :
    (inputs x).length = n + 2 := by simp [inputs]

@[simp] theorem inputs_bit {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (inputs x).getD i.val false = x i := by
  rw [inputs, getD_append_left _ _ _ _ (by simp)]
  simp

@[simp] theorem inputs_false {n : Nat} (x : Fin n → Bool) :
    (inputs x).getD n false = false := by
  rw [inputs, getD_append_right _ _ _ _ (by simp)]
  simp

@[simp] theorem inputs_true {n : Nat} (x : Fin n → Bool) :
    (inputs x).getD (n + 1) false = true := by
  rw [inputs, getD_append_right _ _ _ _ (by simp)]
  simp

def inputWire {m width : Nat} (source : Fin m → Bool ⊕ Fin width) (i : Fin m) : Nat :=
  (source i).elim (fun b => width + b.toNat) Fin.val

theorem inputWire_lt {m width : Nat} (source : Fin m → Bool ⊕ Fin width) (i : Fin m) :
    inputWire source i < width + 2 := by
  unfold inputWire
  cases h : source i with
  | inl b => cases b <;> simp
  | inr j => simpa using (show j.val < width + 2 by omega)

theorem inputWire_value {m width : Nat} (source : Fin m → Bool ⊕ Fin width)
    (x : Fin width → Bool) (i : Fin m) :
    (inputs x).getD (inputWire source i) false = (source i).elim id x := by
  unfold inputWire
  cases h : source i with
  | inl b =>
    cases b
    · change (inputs x).getD (width + 0) false = false
      simpa only [Nat.add_zero] using inputs_false x
    · change (inputs x).getD (width + 1) false = true
      exact inputs_true x
  | inr j =>
    change (inputs x).getD j.val false = x j
    exact inputs_bit x j

def wireMap {m width : Nat} (source : Fin m → Bool ⊕ Fin width) (t : Nat) : Nat :=
  if h : t < m then inputWire source ⟨t, h⟩
  else if t < m + 2 then width + (t - m)
  else width + 2 + (t - (m + 2))

theorem wireMap_input_lt {m width : Nat} (source : Fin m → Bool ⊕ Fin width)
    (t : Nat) (ht : t < m + 2) : wireMap source t < width + 2 := by
  unfold wireMap
  split_ifs with h
  · exact inputWire_lt source ⟨t, h⟩
  · omega

theorem wireMap_gate {m width : Nat} (source : Fin m → Bool ⊕ Fin width) (j : Nat) :
    wireMap source (m + 2 + j) = width + 2 + j := by
  simp [wireMap, show ¬m + 2 + j < m by omega,
    show ¬m + 2 + j < m + 2 by omega]

theorem wireMap_lt {m width s : Nat} (source : Fin m → Bool ⊕ Fin width)
    (t : Nat) (ht : t < m + 2 + s) : wireMap source t < width + 2 + s := by
  by_cases h : t < m + 2
  · have hh := wireMap_input_lt source t h
    omega
  · have he : t = m + 2 + (t - (m + 2)) := by omega
    rw [he, wireMap_gate]
    omega

theorem wireMap_value {m width : Nat} (source : Fin m → Bool ⊕ Fin width)
    (x : Fin width → Bool) (t : Nat) (ht : t < m + 2) :
    (inputs x).getD (wireMap source t) false =
      (inputs (fun i => (source i).elim id x)).getD t false := by
  by_cases h : t < m
  · have hm : wireMap source t = inputWire source ⟨t,h⟩ := by simp [wireMap,h]
    rw [hm, inputWire_value]
    exact (inputs_bit (fun i => (source i).elim id x) ⟨t,h⟩).symm
  · have he : t = m ∨ t = m + 1 := by omega
    rcases he with rfl | rfl
    · have hm : wireMap source t = width := by simp [wireMap]
      rw [hm, inputs_false, inputs_false]
    · have hm : wireMap source (m + 1) = width + 1 := by
        simp [wireMap, show ¬m + 1 < m by omega]
      rw [hm, inputs_true, inputs_true]

set_option maxHeartbeats 800000 in
theorem remap {m width : Nat} (source : Fin m → Bool ⊕ Fin width)
    (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack (m+2) C)
    (hout : C.output < m+2+C.size) :
    ∃ (B : Circuit) (rho : Fin (m+2+C.size) → Fin (width+2+B.size)),
      FanInTwo B ∧ ReadsBack (width+2) B ∧ B.output < width+2+B.size ∧
      B.size = C.size ∧ B.gates.map (fun g => g.op) = C.gates.map (fun g => g.op) ∧
      ∀ (x : Fin width → Bool) (t : Fin (m+2+C.size)),
        (B.wires (inputs x)).getD (rho t).val false =
          (C.wires (inputs (fun i => (source i).elim id x))).getD t.val false := by
  let phi := wireMap source
  let gs := C.gates.map (fun g => (⟨g.op, g.inputs.map phi⟩ : Gate))
  let B : Circuit := ⟨gs, phi C.output⟩
  have hsize : B.size = C.size := by simp [B, gs, Circuit.size]
  have hphi : ∀ t, t < m+2+C.size → phi t < width+2+B.size := by
    intro t ht
    rw [hsize]
    exact wireMap_lt source t ht
  let rho : Fin (m+2+C.size) → Fin (width+2+B.size) :=
    fun t => ⟨phi t.val, hphi t.val t.isLt⟩
  have hf : FanInTwo B := by
    apply fanInTwo_map_inputs
    exact hfan
  have hsim (x : Fin width → Bool) :=
    wiresFrom_remap_full C.gates (inputs (fun i => (source i).elim id x)) (inputs x) phi
      (by simpa only [inputs_length, ReadsBack, gateAt, Circuit.size] using hrb)
      (by intro t ht; simpa using wireMap_input_lt source t (by simpa using ht))
      (by intro j hj; simpa [phi] using wireMap_gate source j)
      (by intro t ht; exact wireMap_value source x t (by simpa using ht))
  refine ⟨B, rho, hf, ?_, hphi C.output hout, hsize, ?_, ?_⟩
  · simpa only [B, gs, inputs_length, ReadsBack, gateAt, Circuit.size] using (hsim (fun _ => false)).1
  · simp [B, gs, List.map_map]
  · intro x t
    exact (hsim x).2 t.val (by simpa [Circuit.size] using t.isLt)

end Lib1218Relabel

namespace Lib1218Relabel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket

theorem notCount_of_ops {B C : Circuit}
    (h : B.gates.map (fun g=>g.op)=C.gates.map (fun g=>g.op)) : notCount B=notCount C := by
  have H := congrArg (fun ops : List GateOp=>(ops.filter (fun op=>
    @decide (op=GateOp.not) (lineDegreeGateOpDecEq op GateOp.not))).length) h
  simpa only [List.filter_map,List.length_map,Function.comp_def,notCount] using H

theorem remap_eval {m width : Nat} (source : Fin m → Bool ⊕ Fin width)
    (C : Circuit) (hfan : FanInTwo C) (hrb : ReadsBack (m+2) C)
    (hout : C.output<m+2+C.size) :
    ∃ (B : Circuit) (rho : Fin (m+2+C.size) → Fin (width+2+B.size)),
      FanInTwo B ∧ ReadsBack (width+2) B ∧ B.output<width+2+B.size ∧
      B.size=C.size ∧ notCount B=notCount C ∧
      (∀ x : Fin width → Bool,B.eval (inputs x)=C.eval (inputs (fun i=>(source i).elim id x))) ∧
      ∀ (x : Fin width → Bool) (t : Fin (m+2+C.size)),
        (B.wires (inputs x)).getD (rho t).val false=
          (C.wires (inputs (fun i=>(source i).elim id x))).getD t.val false := by
  obtain ⟨B0,rho,hf,hr,ho,hs,hops,hsem⟩ := remap source C hfan hrb hout
  let out : Fin (m+2+C.size) := ⟨C.output,hout⟩
  let B : Circuit := ⟨B0.gates,(rho out).val⟩
  have hsize : B.size=B0.size := rfl
  have hn : notCount B=notCount C := by
    change notCount B0=notCount C
    exact notCount_of_ops hops
  refine ⟨B,rho,hf,hr,(rho out).isLt,hsize.trans hs,hn,?_,?_⟩
  · intro x
    change (B0.wires (inputs x)).getD (rho out).val false=
      (C.wires (inputs (fun i=>(source i).elim id x))).getD C.output false
    exact hsem x out
  · intro x t
    change (B0.wires (inputs x)).getD (rho t).val false=_
    exact hsem x t

end Lib1218Relabel

namespace Lib1436Split
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Base

def join {t r : Nat} (x : Input t) (y : Input r) : Input (t+r) := Fin.addCases x y

def source (t r : Nat) : Fin (t+r) → Bool ⊕ Fin t :=
  Fin.addCases Sum.inr (fun _=>Sum.inl false)

theorem source_value {t r : Nat} (x : Input t) :
    (fun i=>(source t r i).elim id x)=join x (fun _ : Fin r=>false) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [source,join,Fin.addCases_left,Sum.elim_inr]
  · intro j
    simp only [source,join,Fin.addCases_right,Sum.elim_inl,id_eq]

theorem split {t r : Nat} (A C : Circuit) (decision : Nat)
    (af : FanInTwo A) (ar : ReadsBack (t+r+2) A) (an : notCount A=0)
    (cf : FanInTwo C) (cr : ReadsBack (t+r+2) C) (cp : A.gates <+: C.gates)
    (dl : decision < nextWire (t+r+2) A)
    (independent : ∀(x : Input t)(y : Input r),
      value A (withConstants (join x y)) decision=
      value A (withConstants (join x (fun _ : Fin r=>false))) decision) :
    ∃S D : Circuit,FanInTwo S ∧ ReadsBack (t+2) S ∧ S.output < t+2+S.size ∧
      notCount S=0 ∧ S.size=A.size ∧ FanInTwo D ∧ ReadsBack (t+r+2) D ∧
      D.output < t+r+2+D.size ∧ D.gates=C.gates ∧ D.size=C.size ∧ notCount D=notCount C ∧
      (∀(x : Input t),S.eval (withConstants x)=
        value A (withConstants (join x (fun _ : Fin r=>false))) decision) ∧
      ∀(x : Input t)(y : Input r),D.eval (withConstants (join x y))=S.eval (withConstants x) := by
  let A' : Circuit := ⟨A.gates,decision⟩
  obtain ⟨S,rho,sf,sr,so,ss,sn,sv,sw⟩ := Lib1218Relabel.remap_eval (source t r) A' af ar dl
  let D : Circuit := ⟨C.gates,decision⟩
  have sval (x : Input t) : S.eval (withConstants x)=
      value A (withConstants (join x (fun _ : Fin r=>false))) decision := by
    have hh := sv x
    rw [source_value] at hh
    exact hh
  refine ⟨S,D,sf,sr,so,sn.trans an,ss,cf,cr,?_,rfl,rfl,rfl,sval,?_⟩
  · exact dl.trans_le (nextWire_le_of_prefix cp)
  · intro x y
    change value C (withConstants (join x y)) decision=_
    rw [value_of_prefix cp (by simpa only [withConstants_length] using dl),independent,sval]

end Lib1436Split

namespace Lib1436Budget

def limit (m r : Nat) : Nat := 64*(r+1)*(m+1)^2+64*(m+1)*2^m

theorem compiled_readout (m r : Nat) :
    2*m*m*r+2*m*r+(7*m+7)*2^m+7*m*m+7*m+1 ≤ limit m r := by
  unfold limit
  calc
    _ ≤ (2*m*m*r+2*m*r+(7*m+7)*2^m+7*m*m+7*m+1) +
        (62*r*m*m+126*r*m+64*r+57*m*m+121*m+63+57*m*2^m+57*2^m) := Nat.le_add_right _ _
    _ = _ := by ring

theorem compiled_size (m r : Nat) :
    2*m*m*r+2*m*r+(7*m+7)*2^m+7*m*m ≤ limit m r := by
  have hh := compiled_readout m r
  omega

end Lib1436Budget

namespace Lib1436Arrays
open Base Lib1436Raw Lib1436Compiled

noncomputable def raw {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat) : List Bool :=
  (List.ofFn (fun i=>(Lib1436Nat.bits r (Z i)).take r)).flatten ++
  (List.ofFn (fun i=>(Lib1436Nat.bits r (O i)).take r)).flatten ++
  (Lib1436Nat.bits m (E false)).take m ++ (Lib1436Nat.bits m (E true)).take m

theorem bits_take (r : Nat) (X : Finset Nat) :
    (Lib1436Nat.bits r X).take r=List.ofFn (fun j : Fin r=>decide (j.val∈X)) := by
  classical
  simp [Lib1436Nat.bits,List.take_append]

theorem raw_eq {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat) :
    raw (r:=r) Z O E=List.ofFn (encode (r:=r) Z O E) := by
  classical
  simp only [raw,bits_take,ofFn_encode]

noncomputable def queryBits {r : Nat} (X : Finset Nat) : Input r := fun j=>decide (j.val∈X)

theorem programme_input {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat) :
    raw (r:=r) Z O E++[false,true]=withConstants (encode (r:=r) Z O E) := by
  rw [raw_eq]
  rfl

theorem full_input {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat) (X : Finset Nat) :
    raw (r:=r) Z O E++Lib1436Nat.bits r X=
      withConstants (join (encode (r:=r) Z O E) (queryBits (r:=r) X)) := by
  rw [withConstants_join,raw_eq]
  rfl

theorem enabled_decode {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat) (y : Input r) :
    Enabled (join (encode Z O E) y)=(fun v i=>i.val∈E v) := by
  classical
  funext v i
  apply propext
  simp [Enabled,decodeEFin,join_en,encode_en]

theorem lower_decode {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat) (y : Input r) :
    Lower (join (encode Z O E) y)=(fun i=>Lib1436Nat.lift r (Finset.range r \ Z i)) := by
  classical
  funext i
  ext v
  simp [Lower,decodeZFin,join_z,encode_z,Lib1436Nat.mem_lift,v.isLt]

theorem upper_decode {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat) (y : Input r) :
    Upper (join (encode Z O E) y)=(fun i=>Lib1436Nat.lift r (O i)) := by
  classical
  funext i
  ext v
  simp [Upper,decodeOFin,join_o,encode_o,Lib1436Nat.mem_lift]

theorem query_decode {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat) (X : Finset Nat) :
    decodeXFin (join (encode Z O E) (queryBits (r:=r) X))=Lib1436Nat.lift r X := by
  classical
  ext v
  simp [decodeXFin,join_query,queryBits,Lib1436Nat.mem_lift]

theorem fit_decode {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat) (y : Input r) (b : Nat) :
    Lib1436Nat.Fit (r:=r) Z O E b ↔
      Lib1436Criterion.ScalarFits (Enabled (join (encode Z O E) y))
        (Lower (join (encode Z O E) y)) (Upper (join (encode Z O E) y)) b := by
  rw [enabled_decode,lower_decode,upper_decode]
  exact Lib1436Nat.fit_iff_scalar Z O E b

theorem box_decode {m r : Nat} (Z O : Fin m→Finset Nat) (E : Bool→Finset Nat)
    (X : Finset Nat) (hX : X⊆Finset.range r) (i : Fin m) :
    Lib1436Boxes.Box (Lower (join (encode Z O E) (queryBits (r:=r) X)))
      (Upper (join (encode Z O E) (queryBits (r:=r) X))) i
      (decodeXFin (join (encode Z O E) (queryBits (r:=r) X))) ↔
        Finset.range r \ Z i⊆X ∧ X⊆O i := by
  rw [lower_decode,upper_decode,query_decode]
  exact and_congr (Lib1436Nat.lift_subset_iff Finset.sdiff_subset) (Lib1436Nat.lift_subset_iff hX)

end Lib1436Arrays

namespace Lib1436Final
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.NotBracket
open Base Lib1436Raw Lib1436Compiled

def Valid (n : Nat) (C : Circuit) : Prop := FanInTwo C ∧ ReadsBack (n+2) C ∧ C.output < n+2+C.size

noncomputable def Good {m r : Nat} (x : Input (t m r+r)) (b : Nat) : Prop :=
  Lib1436Criterion.ScalarFits (Enabled x) (Lower x) (Upper x) b

theorem good_join {m r : Nat} (x : Input (t m r)) (y y' : Input r) (b : Nat) :
    Good (join x y) b ↔ Good (join x y') b := by
  unfold Good Enabled Lower Upper
  rw [decodeEFin_join x y y',decodeZFin_join x y y',decodeOFin_join x y y']

theorem core (m r b : Nat) :
    ∃(S D : Circuit)(out : Nat),Valid (t m r) S ∧ notCount S=0 ∧ S.size≤Lib1436Budget.limit m r ∧
      Valid (t m r+r) D ∧ notCount D≤b ∧ D.size-notCount D≤Lib1436Budget.limit m r ∧
      out < t m r+r+2+D.size ∧
      ∀x : Input (t m r),
        (S.eval (withConstants x)=false ↔ Good (join x (fun _ : Fin r=>false)) b) ∧
        ∀y : Input r,D.eval (withConstants (join x y))=S.eval (withConstants x) ∧
          (Good (join x y) b → ∀j v,Enabled (join x y) v j →
            Lib1436Boxes.Box (Lower (join x y)) (Upper (join x y)) j (decodeXFin (join x y)) →
            value D (withConstants (join x y)) out=v) := by
  classical
  obtain ⟨A,decision,threshold,af,ar,an,az,al,tl,av,tv⟩ := compiled m r b
  have bad_false (z : Input (t m r+r)) : value A (withConstants z) decision=false ↔ Good z b := by
    unfold Good
    rw [Bool.eq_false_iff,ne_eq,av,Lib1436Criterion.scalar_iff]
    simp only [not_or,not_exists,not_and,not_le,Lib1436Boxes.collision_iff_bad]
  have independent (x : Input (t m r)) (y : Input r) :
      value A (withConstants (join x y)) decision=
      value A (withConstants (join x (fun _ : Fin r=>false))) decision := by
    have hh := (bad_false (join x y)).trans ((good_join x y (fun _=>false) b).trans
      (bad_false (join x (fun _ : Fin r=>false))).symm)
    cases h1 : value A (withConstants (join x y)) decision <;>
      cases h2 : value A (withConstants (join x (fun _ : Fin r=>false))) decision <;> simp_all
  obtain ⟨C,out,cf,cr,cp,cn,cz,cl,cv⟩ := Lib1436Decoder.append A threshold
    (fun x=>Enabled x) (fun x=>Lower x) (fun x=>Upper x) (fun x=>decodeXFin x) af ar an tl tv
  obtain ⟨S,D,sf,sr,so,sn,sz,df,dr,dout,dg,ds,dn,sv,dv⟩ :=
    Lib1436Split.split A C decision af ar an cf cr cp al independent
  have ss : S.size≤Lib1436Budget.limit m r := by
    rw [sz]
    exact az.trans (Lib1436Budget.compiled_size m r)
  have dd : D.size-notCount D≤Lib1436Budget.limit m r := by
    rw [ds,dn]
    exact cz.trans ((Nat.add_le_add_right (Nat.add_le_add_right az _) _).trans
      (Lib1436Budget.compiled_readout m r))
  refine ⟨S,D,out,⟨sf,sr,so⟩,sn,ss,⟨df,dr,dout⟩,by simpa only [dn] using cn,dd,
    by simpa only [ds,nextWire] using cl,?_⟩
  intro x
  refine ⟨?_,?_⟩
  · rw [sv]
    exact bad_false _
  · intro y
    refine ⟨dv x y,?_⟩
    intro hgood j v he hbox
    have hh := cv (join x y) hgood j v he hbox
    simpa only [value,Circuit.wires,dg] using hh

theorem final (m r b : Nat) :
    ∃(S D : Circuit)(out : Nat),Valid (t m r) S ∧ notCount S=0 ∧ S.size≤Lib1436Budget.limit m r ∧
      Valid (t m r+r) D ∧ notCount D≤b ∧ D.size-notCount D≤Lib1436Budget.limit m r ∧
      out < t m r+r+2+D.size ∧
      ∀(Z O : Fin m→Finset Nat)(E : Bool→Finset Nat),
        (∀i,Z i⊆Finset.range r ∧ O i⊆Finset.range r) → (∀v,E v⊆Finset.range m) →
        (S.eval (Lib1436Arrays.raw (r:=r) Z O E++[false,true])=false ↔ Lib1436Nat.Fit (r:=r) Z O E b) ∧
        ∀X⊆Finset.range r,
          D.eval (Lib1436Arrays.raw (r:=r) Z O E++Lib1436Nat.bits r X)=
            S.eval (Lib1436Arrays.raw (r:=r) Z O E++[false,true]) ∧
          (Lib1436Nat.Fit (r:=r) Z O E b → ∀i,Finset.range r \ Z i⊆X → X⊆O i → ∀v,i.val∈E v →
            (D.wires (Lib1436Arrays.raw (r:=r) Z O E++Lib1436Nat.bits r X)).getD out false=v) := by
  classical
  obtain ⟨S,D,out,sv,sn,ss,dv,dn,ds,ol,hsem⟩ := core m r b
  refine ⟨S,D,out,sv,sn,ss,dv,dn,ds,ol,?_⟩
  intro Z O E hZO hE
  have hp := hsem (encode (r:=r) Z O E)
  constructor
  · rw [Lib1436Arrays.programme_input]
    exact hp.1.trans (Lib1436Arrays.fit_decode Z O E (fun _ : Fin r=>false) b).symm
  · intro X hX
    have hx := hp.2 (Lib1436Arrays.queryBits (r:=r) X)
    rw [Lib1436Arrays.full_input,Lib1436Arrays.programme_input]
    refine ⟨hx.1,?_⟩
    intro hfit i hlo hhi v hv
    apply hx.2 ((Lib1436Arrays.fit_decode Z O E (Lib1436Arrays.queryBits (r:=r) X) b).mp hfit) i v
    · rw [Lib1436Arrays.enabled_decode]
      exact hv
    · exact (Lib1436Arrays.box_decode Z O E X hX i).mpr ⟨hlo,hhi⟩

end Lib1436Final

end PEqualNP.Outside.L_lib_1436_aux

open PEqualNP.Outside.L_lib_1436_aux in
theorem PEqualNP.Outside.L_lib_1436 :
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let bits := fun (r : Nat) (Y : Finset Nat) => List.ofFn (fun j : Fin r => decide (j.val ∈ Y)) ++ [false,true]
  let valid := fun (r : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧ D.output < r+2+D.size
  ∀ (m r b : Nat),
    let t := 2*m*r+2*m
    let B := 64*(r+1)*(m+1)^2+64*(m+1)*2^m
    let fit := fun (Z O : Fin m → Finset Nat) (E : Bool → Finset Nat) =>
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, valid r C ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
        ∀ X ⊆ Finset.range r, ∀ i : Fin m, Finset.range r \ Z i ⊆ X → X ⊆ O i →
          ∀ v : Bool, i.val ∈ E v → C.eval (bits r X)=v
    ∃ (S D : PEqualNP.CircuitLowerBounds.Circuit) (out : Nat),
      valid t S ∧ PEqualNP.NotBracket.notCount S=0 ∧ S.size ≤ B ∧ valid (t+r) D ∧
      PEqualNP.NotBracket.notCount D ≤ b ∧ D.size-PEqualNP.NotBracket.notCount D ≤ B ∧ out<t+r+2+D.size ∧
      ∀ (Z O : Fin m → Finset Nat) (E : Bool → Finset Nat),
        (∀ i, Z i ⊆ Finset.range r ∧ O i ⊆ Finset.range r) → (∀ v, E v ⊆ Finset.range m) →
        let raw := (List.ofFn (fun i => (bits r (Z i)).take r)).flatten ++
          (List.ofFn (fun i => (bits r (O i)).take r)).flatten ++
          (bits m (E false)).take m ++ (bits m (E true)).take m
        (S.eval (raw ++ [false,true])=false ↔ fit Z O E) ∧
        ∀ X ⊆ Finset.range r,
          let I := raw ++ bits r X
          D.eval I=S.eval (raw ++ [false,true]) ∧
          (fit Z O E → ∀ i : Fin m, Finset.range r \ Z i ⊆ X → X ⊆ O i → ∀ v : Bool, i.val ∈ E v →
            (D.wires I).getD out false=v)
:= by
  classical
  dsimp only
  intro m r b
  have hall := Lib1436Final.final m r b
  unfold Lib1436Final.Valid Lib1436Raw.t Lib1436Budget.limit at hall
  unfold Lib1436Arrays.raw Lib1436Nat.Fit Lib1436Nat.bits at hall
  simp only [and_assoc] at hall ⊢
  convert hall using 1 <;> congr! 48
  all_goals try simp only [decide_eq_decide]
