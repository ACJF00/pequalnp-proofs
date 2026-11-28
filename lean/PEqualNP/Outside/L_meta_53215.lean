import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53215
open Finset

variable {n c : ℕ}

private def fiber (a : Fin n → Fin c) (j : Fin c) : Finset (Fin n) :=
  univ.filter (fun i => a i = j)

@[simp] private theorem mem_fiber {a : Fin n → Fin c} {j i} :
    i ∈ fiber a j ↔ a i = j := by simp [fiber]

private def full (a : Fin n → Fin c) (x : Finset (Fin n)) : Finset (Fin c) :=
  univ.filter fun j => fiber a j ⊆ x

@[simp] private theorem mem_full {a : Fin n → Fin c} {j x} :
    j ∈ full a x ↔ fiber a j ⊆ x := by simp [full]

private def normal (a : Fin n → Fin c) (x : Finset (Fin n)) : Finset (Fin n) :=
  x.filter fun i => ¬ fiber a (a i) ⊆ x

@[simp] private theorem mem_normal {a : Fin n → Fin c} {i x} :
    i ∈ normal a x ↔ i ∈ x ∧ ¬ fiber a (a i) ⊆ x := by simp [normal]

private theorem no_full_normal {a : Fin n → Fin c} (ha : Function.Surjective a)
    (x : Finset (Fin n)) (j : Fin c) : ¬ fiber a j ⊆ normal a x := by
  intro h
  obtain ⟨i, hi⟩ := ha j
  obtain ⟨_, hn⟩ := mem_normal.mp (h (mem_fiber.mpr hi))
  rw [hi] at hn
  exact hn (h.trans (filter_subset _ _))

@[simp] private theorem normal_normal {a : Fin n → Fin c} (ha : Function.Surjective a)
    (x : Finset (Fin n)) : normal a (normal a x) = normal a x := by
  ext i
  rw [mem_normal]
  simp only [no_full_normal ha, not_false_eq_true, and_true]

private theorem full_union {a : Fin n → Fin c} (x : Finset (Fin n)) (j : Fin c) :
    full a (x ∪ fiber a j) = insert j (full a x) := by
  ext k
  simp only [mem_full, mem_insert]
  by_cases hk : k = j
  · subst k
    simp
  · simp only [hk, false_or]
    constructor
    · intro h i hi
      rcases mem_union.mp (h hi) with hh | hh
      · exact hh
      · exact (hk ((mem_fiber.mp hi).symm.trans (mem_fiber.mp hh))).elim
    · exact fun h => h.trans subset_union_left

private theorem normal_union {a : Fin n → Fin c} {x : Finset (Fin n)} {j : Fin c}
    (hd : Disjoint x (fiber a j)) : normal a (x ∪ fiber a j) = normal a x := by
  ext i
  simp only [mem_normal, ← mem_full, full_union, mem_insert, mem_union, mem_fiber]
  by_cases hi : a i = j
  · simp [hi, show i ∉ x from fun h => disjoint_left.mp hd h (mem_fiber.mpr hi)]
  · simp [hi]

private def hasFlips (a : Fin n → Fin c) (A : Finset (Finset (Fin n))) :=
  ∀ j, ∃ x ∈ A, Disjoint x (fiber a j) ∧ x ∪ fiber a j ∈ A

private theorem many_rows {a : Fin n → Fin c} (ha : Function.Surjective a)
    {A : Finset (Finset (Fin n))} (hf : hasFlips a A) :
    c + (A.image (normal a)).card ≤ A.card := by
  classical
  let key (J : Finset (Fin c)) (x : Finset (Fin n)) := (normal a x, full a x \ J)
  have bound (J : Finset (Fin c)) : J.card + (A.image (key J)).card ≤ A.card := by
    induction J using Finset.induction_on with
    | empty => simpa using (Finset.card_image_le (s := A) (f := key ∅))
    | @insert j J hj ih =>
      let drop (q : Finset (Fin n) × Finset (Fin c)) := (q.1, q.2.erase j)
      have step (x : Finset (Fin n)) : drop (key J x) = key (insert j J) x := by
        refine Prod.ext rfl ?_
        ext k
        simp [key, drop, and_assoc, and_comm, eq_comm]
      have him : (A.image (key J)).image drop = A.image (key (insert j J)) := by
        rw [image_image]
        exact Finset.image_congr fun x _ => step x
      have lt : ((A.image (key J)).image drop).card < (A.image (key J)).card := by
        apply lt_of_le_of_ne card_image_le
        intro he
        have inj := card_image_iff.mp he
        obtain ⟨x, hx, hd, htop⟩ := hf j
        have hlow : j ∉ full a x := by
          obtain ⟨i, hi⟩ := ha j
          have hmem := mem_fiber.mpr hi
          exact fun h => disjoint_left.mp hd (mem_full.mp h hmem) hmem
        have collapse : drop (key J x) = drop (key J (x ∪ fiber a j)) := by
          rw [step, step]
          apply Prod.ext
          · exact (normal_union hd).symm
          · change full a x \ insert j J = full a (x ∪ fiber a j) \ insert j J
            rw [full_union]
            ext k
            simp
        have equal := inj (mem_image_of_mem (key J) hx) (mem_image_of_mem (key J) htop) collapse
        have e := congrArg Prod.snd equal
        change full a x \ J = full a (x ∪ fiber a j) \ J at e
        have hhigh : j ∈ full a (x ∪ fiber a j) \ J := by simp [full_union, hj]
        exact hlow (mem_sdiff.mp (e ▸ hhigh)).1
      rw [him] at lt
      rw [card_insert_of_notMem hj]
      omega
  have h := bound univ
  have same : (A.image (key univ)).image Prod.fst = A.image (normal a) := by
    rw [image_image]
    rfl
  have le : (A.image (normal a)).card ≤ (A.image (key univ)).card :=
    same ▸ card_image_le
  simpa using (Nat.add_le_add_left le (univ : Finset (Fin c)).card).trans h

private theorem normal_fixed {a : Fin n → Fin c} (ha : Function.Surjective a)
    {P : Finset (Finset (Fin n))} (hp : P.image (normal a) = P)
    {x} (hx : x ∈ P) : normal a x = x := by
  rw [← hp] at hx
  obtain ⟨y, _, rfl⟩ := mem_image.mp hx
  exact normal_normal ha y

private theorem build_rows {a : Fin n → Fin c} (ha : Function.Surjective a)
    {P : Finset (Finset (Fin n))} (hp : P.image (normal a) = P)
    (s : Fin c → Finset (Fin n)) (hs : ∀ j, s j ∈ P ∧ Disjoint (s j) (fiber a j)) :
    let B := P ∪ univ.image (fun j => s j ∪ fiber a j)
    B.image (normal a) = P ∧ hasFlips a B ∧ B.card = c + P.card := by
  classical
  let top (j : Fin c) := s j ∪ fiber a j
  let B := P ∪ univ.image top
  change B.image (normal a) = P ∧ hasFlips a B ∧ B.card = c + P.card
  have htop (j) : normal a (top j) = s j :=
    (normal_union (hs j).2).trans (normal_fixed ha hp (hs j).1)
  have hImage : B.image (normal a) = P := by
    apply subset_antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      rcases mem_union.mp hx with h | h
      · simpa [normal_fixed ha hp h] using h
      · obtain ⟨j, _, rfl⟩ := mem_image.mp h
        simpa only [htop] using (hs j).1
    · intro y hy
      exact mem_image.mpr ⟨y, mem_union_left _ hy, normal_fixed ha hp hy⟩
  have hf : hasFlips a B := fun j =>
    ⟨s j, mem_union_left _ (hs j).1, (hs j).2, mem_union_right _ (mem_image_of_mem top (mem_univ j))⟩
  refine ⟨hImage, hf, le_antisymm ?_ ?_⟩
  · calc
      B.card ≤ P.card + (univ.image top).card := card_union_le _ _
      _ ≤ P.card + (univ : Finset (Fin c)).card := Nat.add_le_add_left card_image_le _
      _ = c + P.card := by simp [Nat.add_comm]
  · simpa only [hImage] using many_rows ha hf

private abbrev Row (n : ℕ) := Finset (Fin n)
private abbrev Col (n : ℕ) := Row n → Bool

private def val (f : Col n) (x : Row n) : ℤ := (f x).toNat

private def changeAt (a : Fin n → Fin c) (f : Col n) (j : Fin c) : ℤ :=
  val f (fiber a j) - val f ∅

private def regular (a : Fin n → Fin c) (f : Col n) : Prop :=
  ∀ x, val f x - val f (normal a x) = ∑ j ∈ full a x, changeAt a f j

private theorem reg_const (a : Fin n → Fin c) (b : Bool) :
    regular a (fun _ => b) := by
  intro x
  simp [changeAt, val]

private theorem reg_two (a : Fin n → Fin c) (i k : Fin n) (h : a k = a i)
    (F : Bool → Bool → Bool) :
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    regular a (fun x => F (decide (i ∈ x)) (decide (k ∈ x))) := by
  let : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let f : Col n := fun x => F (decide (i ∈ x)) (decide (k ∈ x))
  let d : ℤ := ((F true true).toNat : ℤ) - ((F false false).toNat : ℤ)
  have delta (j) : changeAt a f j = if j = a i then d else 0 := by
    by_cases hj : j = a i
    · subst j
      simp [changeAt, val, f, d, h]
    · simp [changeAt, val, f, h, Ne.symm hj, hj]
  intro x
  change val f x - val f (normal a x) = ∑ j ∈ full a x, changeAt a f j
  simp_rw [delta]
  rw [Finset.sum_ite_eq']
  by_cases hi : fiber a (a i) ⊆ x
  · have hix := hi (mem_fiber.mpr (rfl : a i = a i))
    have hkx := hi (mem_fiber.mpr h)
    simp [val, f, d, h, hix, hkx, hi]
  · simp [val, f, h, hi]

private theorem reg_step {a : Fin n → Fin c} (ha : Function.Surjective a)
    {f : Col n} (hr : regular a f) {x j} (hd : Disjoint x (fiber a j)) :
    val f (x ∪ fiber a j) - val f x = changeAt a f j := by
  have hj : j ∉ full a x := by
    obtain ⟨i, hi⟩ := ha j
    have hm := mem_fiber.mpr hi
    exact fun h => disjoint_left.mp hd (mem_full.mp h hm) hm
  have h := hr (x ∪ fiber a j)
  rw [normal_union hd, full_union, sum_insert hj] at h
  have l := hr x
  omega

private theorem value_eq_iff {f g : Col n} {x y} :
    val f x = val g y ↔ f x = g y := by
  cases h : f x <;> cases k : g y <;> simp [val, h, k]

private theorem transport {a : Fin n → Fin c} {f g : Col n}
    (hf : regular a f) (hg : regular a g) (he : changeAt a f = changeAt a g) (x : Row n) :
    f (normal a x) = g (normal a x) ↔ f x = g x := by
  have h := hf x
  have k := hg x
  simp only [he] at h
  rw [← value_eq_iff, ← value_eq_iff]
  omega

private def compared (raw need : Finset (Col n)) (f g : Col n) :=
  f ∈ need ∧ (g ∈ raw ∨ (g ∈ need ∧ f ≠ g))

private def separated (raw need : Finset (Col n)) (A : Finset (Row n)) :=
  ∀ f g, compared raw need f g → ∃ x ∈ A, f x ≠ g x

private def adm (a : Fin n → Fin c) (raw need : Finset (Col n)) (P : Finset (Row n)) :=
  P.image (normal a) = P ∧ (∀ j, ∃ z ∈ P, Disjoint z (fiber a j)) ∧
  ∀ f ∈ need, ∀ g, (g ∈ raw ∨ (g ∈ need ∧ f ≠ g)) →
    changeAt a f = changeAt a g → ∃ z ∈ P, f z ≠ g z

private theorem split_comparisons {a : Fin n → Fin c} (ha : Function.Surjective a)
    {raw need : Finset (Col n)} (hr : ∀ f ∈ raw ∪ need, regular a f) (A : Finset (Row n)) :
    (separated raw need A ∧ hasFlips a A) ↔ adm a raw need (A.image (normal a)) ∧ hasFlips a A := by
  classical
  have regs {f g} (hf : f ∈ need) (hg : g ∈ raw ∨ (g ∈ need ∧ f ≠ g)) :
      regular a f ∧ regular a g :=
    ⟨hr _ (mem_union_right _ hf), hr _ (mem_union.mpr (hg.imp_right And.left))⟩
  constructor
  · rintro ⟨hsep, hflip⟩
    refine ⟨⟨?_, ?_, ?_⟩, hflip⟩
    · rw [image_image]
      exact image_congr (fun x _ => normal_normal ha x)
    · intro j
      obtain ⟨x, hx, hd, _⟩ := hflip j
      exact ⟨_, mem_image_of_mem _ hx, Disjoint.mono_left (filter_subset _ _) hd⟩
    · intro f hf g hg he
      obtain ⟨x, hx, hfg⟩ := hsep f g ⟨hf, hg⟩
      obtain ⟨rf, rg⟩ := regs hf hg
      exact ⟨_, mem_image_of_mem _ hx, fun hh => hfg ((transport rf rg he x).mp hh)⟩
  · rintro ⟨⟨_, _, hsep⟩, hflip⟩
    refine ⟨?_, hflip⟩
    rintro f g ⟨hf, hg⟩
    obtain ⟨rf, rg⟩ := regs hf hg
    by_cases he : changeAt a f = changeAt a g
    · obtain ⟨z, hz, hfg⟩ := hsep f hf g hg he
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
      exact ⟨x, hx, fun hh => hfg ((transport rf rg he x).mpr hh)⟩
    · by_contra! h
      apply he
      funext j
      obtain ⟨x, hx, hd, htop⟩ := hflip j
      rw [← reg_step ha rf hd, ← reg_step ha rg hd,
        value_eq_iff.mpr (h _ htop), value_eq_iff.mpr (h _ hx)]

private theorem from_bank {a : Fin n → Fin c} (ha : Function.Surjective a)
    {raw need : Finset (Col n)} (hr : ∀ f ∈ raw ∪ need, regular a f)
    (keeps : Finset (Row n) → Prop)
    (bank : ∀ A, keeps A ↔ separated raw need A ∧ hasFlips a A) :
    (∀ A, keeps A ↔ adm a raw need (A.image (normal a)) ∧ hasFlips a A) ∧
    (∀ P b, (∃ A, A.image (normal a) = P ∧ keeps A ∧ A.card ≤ b) ↔
      adm a raw need P ∧ c + P.card ≤ b) ∧
    ∀ P, adm a raw need P → ∀ s : Fin c → Row n,
      (∀ j, s j ∈ P ∧ Disjoint (s j) (fiber a j)) →
      let B := P ∪ univ.image (fun j => s j ∪ fiber a j)
      B.image (normal a) = P ∧ keeps B ∧ B.card = c + P.card := by
  classical
  have h1 (A) := (bank A).trans (split_comparisons ha hr A)
  have h3 (P) (hp : adm a raw need P) (s : Fin c → Row n) (hs : ∀ j, s j ∈ P ∧ Disjoint (s j) (fiber a j)) := by
    obtain ⟨him, hf, hc⟩ := build_rows ha hp.1 s hs
    exact And.intro him (And.intro ((h1 _).mpr ⟨him.symm ▸ hp, hf⟩) hc)
  refine ⟨h1, ?_, h3⟩
  intro P b
  constructor
  · rintro ⟨A, rfl, h, hb⟩
    obtain ⟨hp, hf⟩ := (h1 A).mp h
    exact ⟨hp, (many_rows ha hf).trans hb⟩
  · rintro ⟨hp, hb⟩
    choose s hs hd using hp.2.1
    obtain ⟨him, hk, hc⟩ := h3 P hp s (fun j => ⟨hs j, hd j⟩)
    exact ⟨_, him, hk, hc.trans_le hb⟩

private theorem graph_regular (E : Finset (Fin n × Fin n)) (a : Fin n → Fin c)
    (conn : ∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, a i = a j → (i ∈ Z ↔ j ∈ Z)) :
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    let bit := fun (i : Fin n) (x : Row n) => decide (i ∈ x)
    let neg := fun (i : Fin n) (x : Row n) => !(bit i x)
    let same := fun (e : Fin n × Fin n) (x : Row n) => bit e.1 x == bit e.2 x
    let raw : Finset (Col n) := {fun _ => false,fun _ => true} ∪ univ.image bit ∪
      E.image same ∪ E.image (fun e x => !(same e x))
    let need := univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
      E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
    ∀ f ∈ raw ∪ need, regular a f := by
  classical
  intro bit neg same raw need f hf
  have edge (e) (he : e ∈ E) : a e.2 = a e.1 := by
    have h := (conn (fiber a (a e.1))).mpr (fun i k h => by simp only [mem_fiber]; rw [h])
    exact mem_fiber.mp ((h e he).mp (mem_fiber.mpr rfl))
  simp only [raw, need, mem_union, mem_insert, mem_singleton, mem_image, mem_univ, true_and] at hf
  rcases hf with (((((rfl | rfl) | ⟨i, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) |
    (((⟨i, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩))
  · exact reg_const a false
  · exact reg_const a true
  · exact reg_two a i i rfl (fun b _ => b)
  · convert reg_two a e.1 e.2 (edge e he) (fun b d => b == d) using 1
    funext x
    dsimp only [same, bit]
    congr!
  · convert reg_two a e.1 e.2 (edge e he) (fun b d => !(b == d)) using 1
    funext x
    dsimp only [same, bit]
    congr!
  · exact reg_two a i i rfl (fun b _ => !b)
  · exact reg_two a e.1 e.2 (edge e he) (fun b d => !b && !d)
  · exact reg_two a e.1 e.2 (edge e he) (fun b d => b && !d)
  · exact reg_two a e.1 e.2 (edge e he) (fun b d => !b && d)

open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
noncomputable section
variable {X : Type}

private def mix (b : Bool) (f g : X → Bool) : X → Bool :=
  fun x => if b then f x && g x else f x || g x

private def wire (L : List (X → Bool)) (C : Circuit) (j : ℕ) : X → Bool :=
  fun x => (C.wires (L.map fun f => f x)).getD j false

private def fits (L : List (X → Bool)) (D : Finset (X → Bool)) (p : ℕ) :=
  ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack L.length C ∧
    C.output < L.length + C.size ∧ C.size ≤ p ∧ ∀ f ∈ D, ∃ j < L.length + C.size, wire L C j = f

private theorem wires_tail (C : Circuit) (v : List Bool) :
    ∃ t : List Bool, C.wires v = v ++ t ∧ t.length = C.size := by
  obtain ⟨G, o⟩ := C
  induction G generalizing v with
  | nil => exact ⟨[], by simp [Circuit.wires], rfl⟩
  | cons g G ih =>
    let u := g.op.eval (g.inputs.map fun i => v.getD i false)
    obtain ⟨t, he, hl⟩ := ih (v ++ [u])
    exact ⟨u :: t, he.trans (by simp), by simpa [Circuit.size] using hl⟩

private theorem wire_length (C : Circuit) (v) : (C.wires v).length = v.length + C.size := by
  obtain ⟨t, he, hl⟩ := wires_tail C v
  simp [he, hl]

private theorem wire_at_input (L : List (X → Bool)) (C : Circuit) {j : ℕ} (hj : j < L.length) :
    wire L C j = L[j] := by
  funext x
  obtain ⟨t, he, _⟩ := wires_tail C (L.map fun f => f x)
  unfold wire
  rw [he, List.getD_append _ _ _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]

private theorem wires_needed [DecidableEq (X → Bool)] (L : List (X → Bool)) (D : Finset (X → Bool)) {p} (h : fits L D p) :
    (D \ L.toFinset).card ≤ p := by
  classical
  obtain ⟨C, _, _, _, hsize, hrep⟩ := h
  let gate (i : ℕ) := wire L C (L.length + i)
  have sub : D \ L.toFinset ⊆ (range C.size).image gate := by
    intro f hf
    obtain ⟨hf, hn⟩ := mem_sdiff.mp hf
    obtain ⟨j, hj, rfl⟩ := hrep f hf
    by_cases hi : j < L.length
    · exact (hn (by simp [wire_at_input L C hi])).elim
    · refine mem_image.mpr ⟨j - L.length, mem_range.mpr (by omega), ?_⟩
      unfold gate
      congr 1
      omega
  exact (card_le_card sub).trans ((card_image_le.trans_eq (card_range _)).trans hsize)

private def snocGate (C : Circuit) (b : Bool) (j k : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨if b then .and else .or, [j,k]⟩], C.output⟩

@[simp] private theorem snoc_size (C : Circuit) (b j k) : (snocGate C b j k).size = C.size + 1 := by
  simp [snocGate, Circuit.size]

private theorem snoc_ok {C : Circuit} {m : ℕ} (hm : Monotone2 C) (hb : NestedCover.ReadsBack m C)
    {j k} (hj : j < m + C.size) (hk : k < m + C.size) (b) :
    Monotone2 (snocGate C b j k) ∧ NestedCover.ReadsBack m (snocGate C b j k) := by
  let G : Gate := ⟨if b then .and else .or, [j,k]⟩
  constructor
  · intro g hg
    change g ∈ C.gates ++ [G] at hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with h | rfl
    · exact hm g h
    · cases b <;> simp [G]
  · intro i hi l hl
    change l ∈ ((C.gates ++ [G]).getD i _).inputs at hl
    by_cases hh : i < C.gates.length
    · rw [List.getD_append _ _ _ _ hh] at hl
      exact hb i hh l hl
    · simp only [snocGate, List.length_append, List.length_singleton] at hi
      have e : i = C.gates.length := by omega
      subst i
      simp [G] at hl
      rcases hl with rfl | rfl
      · exact hj
      · exact hk

private theorem snoc_wires (C : Circuit) (b j k) (v : List Bool) :
    (snocGate C b j k).wires v = C.wires v ++
      [if b then (C.wires v).getD j false && (C.wires v).getD k false
        else (C.wires v).getD j false || (C.wires v).getD k false] := by
  cases b <;> simp [snocGate, Circuit.wires, List.foldl_append, GateOp.eval]

private theorem snoc_old (L : List (X → Bool)) (C : Circuit) (b j k) {i}
    (hi : i < L.length + C.size) :
    wire L (snocGate C b j k) i = wire L C i := by
  funext x
  unfold wire
  rw [snoc_wires, List.getD_append _ _ _ _ (by simpa [wire_length] using hi)]

private theorem snoc_last (L : List (X → Bool)) (C : Circuit) (b j k) :
    wire L (snocGate C b j k) (L.length + C.size) = mix b (wire L C j) (wire L C k) := by
  funext x
  simp [wire, snoc_wires, wire_length, mix]

private def derivable (L : List (X → Bool)) (D : Finset (X → Bool)) : Prop :=
  ∀ U : Set (X → Bool), (∀ f ∈ L, f ∈ U) →
    (∀ b f, f ∈ U → ∀ g, g ∈ U → mix b f g ∈ D → mix b f g ∈ U) → ∀ f ∈ D, f ∈ U

private theorem synthesize [DecidableEq (X → Bool)] (L : List (X → Bool)) (hL : 0 < L.length) (D : Finset (X → Bool))
    (hgen : derivable L D) :
    fits L D (D \ L.toFinset).card := by
  classical
  let represented (C : Circuit) (f : X → Bool) := ∃ j < L.length + C.size, wire L C j = f
  have run (R : Finset (X → Bool)) (C : Circuit) (hm : Monotone2 C) (hb : NestedCover.ReadsBack L.length C)
      (hout : C.output < L.length + C.size)
      (hR : ∀ f ∈ D, f ∉ R → represented C f) : fits L D (C.size + R.card) := by
    induction R using Finset.strongInductionOn generalizing C with
    | _ R ih =>
      by_cases done : ∀ f ∈ D, represented C f
      · exact ⟨C, hm, hb, hout, by omega, done⟩
      have hInput : ∀ f ∈ L, represented C f := by
        intro f hf
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hf
        exact ⟨j, by omega, wire_at_input L C hj⟩
      have someGate : ∃ b f g, represented C f ∧ represented C g ∧
          mix b f g ∈ D ∧ ¬ represented C (mix b f g) := by
        by_contra! h
        exact done (hgen {q | represented C q} hInput (fun b f hf g hg hd => h b f g hf hg hd))
      obtain ⟨b,f,g,⟨j,hj,hf⟩,⟨k,hk,hg⟩,ht,hn⟩ := someGate
      let t := mix b f g
      have hmem : t ∈ R := by_contra fun h => hn (hR _ ht h)
      let C' := snocGate C b j k
      obtain ⟨hm', hb'⟩ := snoc_ok hm hb hj hk b
      have hsz : C'.size = C.size + 1 := snoc_size ..
      have hout' : C'.output < L.length + C'.size := by change C.output < _; omega
      have hr' (q) (hq : q ∈ D) (hqr : q ∉ R.erase t) : represented C' q := by
        by_cases e : q = t
        · refine ⟨L.length+C.size, by omega, ?_⟩
          rw [snoc_last, hf, hg, e]
        · obtain ⟨l, hl, hlq⟩ := hR q hq (by simpa [e] using hqr)
          exact ⟨l, by omega, (snoc_old L C b j k hl).trans hlq⟩
      have H := ih (R.erase t) (erase_ssubset hmem) C' hm' hb' hout' hr'
      have hcard := Finset.card_erase_add_one hmem
      rwa [show C.size+R.card = C'.size+(R.erase t).card by omega]
  let C : Circuit := ⟨[],0⟩
  have hm : Monotone2 C := by simp [C, Monotone2]
  have hb : NestedCover.ReadsBack L.length C := by simp [C, NestedCover.ReadsBack]
  have hout : C.output < L.length + C.size := by simpa [C, Circuit.size]
  have H := run (D \ L.toFinset) C hm hb hout (by
    intro f hf h
    have hfL : f ∈ L := by simpa [hf] using h
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hfL
    exact ⟨j, by omega, wire_at_input L C hj⟩)
  simpa [C, Circuit.size] using H

private theorem wires_monotone {L : List (X → Bool)} {D p x y} (h : fits L D p)
    (hxy : ∀ f ∈ L, f x = true → f y = true) : ∀ f ∈ D, f x = true → f y = true := by
  obtain ⟨C, hmon, _, _, _, hrep⟩ := h
  let ordered (u v : List Bool) := u.length = v.length ∧ ∀ j, u.getD j false = true → v.getD j false = true
  have foldmono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (u v : List Bool) (ho : ordered u v) :
      ordered ((Circuit.mk gs 0).wires u) ((Circuit.mk gs 0).wires v) := by
    induction gs generalizing u v with
    | nil => exact ho
    | cons g gs ih =>
      apply ih (fun g' hg => hm g' (List.mem_cons_of_mem _ hg))
      obtain ⟨hl, hh⟩ := ho
      let out (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have hout : out u = true → out v = true := by
        rcases hm g (List.mem_cons_self) with h | h
        · simpa [out, h, GateOp.eval] using fun (hg : ∀ a ∈ g.inputs, u.getD a false = true)
              a ha => hh a (hg a ha)
        · simp [out, h, GateOp.eval]
          exact fun a ha h => ⟨a, ha, hh a h⟩
      change ordered (u ++ [out u]) (v ++ [out v])
      refine ⟨by simp [hl], ?_⟩
      intro j
      by_cases hj : j < u.length
      · rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (hl ▸ hj)]
        exact hh j
      · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hj),
          List.getD_append_right _ _ _ _ (hl ▸ Nat.le_of_not_gt hj), ← hl]
        by_cases he : j - u.length = 0
        · simpa [he] using hout
        · cases e : j - u.length <;> simp_all
  have ho : ordered (L.map (fun f => f x)) (L.map (fun f => f y)) := by
    refine ⟨by simp, ?_⟩
    intro j
    by_cases hj : j < L.length
    · simpa [List.getD_eq_getElem, hj] using hxy L[j] (List.getElem_mem hj)
    · simp [Nat.le_of_not_gt hj]
  have H := foldmono C.gates (fun g hg => (hmon g hg).1) _ _ ho
  intro f hf
  obtain ⟨j, _, rfl⟩ := hrep _ hf
  exact H.2 j

private theorem fits_all [Fintype X] [DecidableEq X] (L : List (X → Bool)) (hf : (fun _ => false) ∈ L)
    (ht : (fun _ => true) ∈ L)
    (antichain : ∀ x y, (∀ f ∈ L, f x = true → f y = true) → x = y) :
    ∃ p, fits L univ p := by
  classical
  apply Exists.intro _
  apply synthesize L (List.length_pos_of_mem hf)
  intro U input gate f _
  have and_closed {g h : X → Bool} (hg : g ∈ U) (hh : h ∈ U) : (fun x => g x && h x) ∈ U :=
    gate true g hg h hh (mem_univ _)
  have or_closed {g h : X → Bool} (hg : g ∈ U) (hh : h ∈ U) : (fun x => g x || h x) ∈ U :=
    gate false g hg h hh (mem_univ _)
  have allU (l : List (X → Bool)) (hl : ∀ g ∈ l, g ∈ U) : (fun x => l.all fun g => g x) ∈ U := by
    induction l with
    | nil => exact input _ ht
    | cons h t ih => exact and_closed (hl _ List.mem_cons_self) (ih (fun _ hg => hl _ (List.mem_cons_of_mem _ hg)))
  have anyU (l : List (X → Bool)) (hl : ∀ g ∈ l, g ∈ U) : (fun x => l.any fun g => g x) ∈ U := by
    induction l with
    | nil => exact input _ hf
    | cons h t ih => exact or_closed (hl _ List.mem_cons_self) (ih (fun _ hg => hl _ (List.mem_cons_of_mem _ hg)))
  let atom (x y : X) := decide (x = y)
  have singletonU (x) : atom x ∈ U := by
    have h := allU (L.filter fun g => g x) (fun _ hg => input _ (List.mem_filter.mp hg).1)
    convert h using 1
    funext y
    apply Bool.eq_iff_iff.mpr
    simp [atom, List.all_eq_true]
    constructor
    · rintro rfl g _
      cases g x <;> simp
    · intro h
      exact antichain x y (fun g hg htrue => (h g hg).resolve_left (by simp [htrue]))
  let rows := (univ.filter (fun x => f x = true)).toList
  have h := anyU (rows.map atom) (by simpa using fun x (_ : x ∈ rows) => singletonU x)
  convert h using 1
  funext y
  apply Bool.eq_iff_iff.mpr
  simp [atom, rows]

end

open Finset
noncomputable section
variable {n c : ℕ}

private abbrev Edge (n : ℕ) := Fin n × Fin n
private abbrev Input (n : ℕ) := Finset (Fin n)
private abbrev Column (n : ℕ) := Input n → Bool

private def pos (i : Fin n) (x : Input n) := decide (i ∈ x)
private def lit (i : Fin n) (x : Input n) := !pos i x
private def parity (e : Edge n) (x : Input n) := pos e.1 x == pos e.2 x
private def diff (e : Edge n) (x : Input n) := !parity e x

private inductive Label (n : ℕ) where
  | neg (i : Fin n)
  | low (e : Edge n)
  | left (e : Edge n)
  | right (e : Edge n)
  deriving DecidableEq

private def column : Label n → Column n
  | .neg i => lit i
  | .low e => fun x => lit e.1 x && lit e.2 x
  | .left e => fun x => pos e.1 x && lit e.2 x
  | .right e => fun x => lit e.1 x && pos e.2 x

private def codes (S : Input n) (E : Finset (Edge n)) : Finset (Label n) :=
  (univ \ S).image Label.neg ∪ E.image Label.low ∪ E.image Label.left ∪ E.image Label.right

@[simp] private theorem codes_neg {S : Input n} {E i} : Label.neg i ∈ codes S E ↔ i ∉ S := by
  simp [codes]
@[simp] private theorem codes_low {S : Input n} {E e} : Label.low e ∈ codes S E ↔ e ∈ E := by
  simp [codes]
@[simp] private theorem codes_left {S : Input n} {E e} : Label.left e ∈ codes S E ↔ e ∈ E := by
  simp [codes]
@[simp] private theorem codes_right {S : Input n} {E e} : Label.right e ∈ codes S E ↔ e ∈ E := by
  simp [codes]

private def constraints : Label n → Input n × Input n
  | .neg i => (∅, {i})
  | .low e => (∅, {e.1,e.2})
  | .left e => ({e.1}, {e.2})
  | .right e => ({e.2}, {e.1})

private theorem cube_rep (t : Label n) (x : Input n) : column t x = true ↔
    (constraints t).1 ⊆ x ∧ Disjoint (constraints t).2 x := by
  cases t <;> simp [column, constraints, pos, lit, and_comm]

private theorem cube_disjoint {S : Input n} {E : Finset (Edge n)}
    (ordered : ∀ e ∈ E, e.1 < e.2) (t : Label n) (ht : t ∈ codes S E) :
    Disjoint (constraints t).1 (constraints t).2 := by
  cases t with
  | neg i => simp [constraints]
  | low e => simp [constraints]
  | left e => simpa [constraints] using (ordered e (codes_left.mp ht)).ne
  | right e => simpa [constraints] using (ordered e (codes_right.mp ht)).ne'

private theorem cube_unique {p q p' q' : Input n} (hd : Disjoint p q) (hd' : Disjoint p' q')
    (he : ∀ x, (p ⊆ x ∧ Disjoint q x) ↔ (p' ⊆ x ∧ Disjoint q' x)) :
    p = p' ∧ q = q' := by
  refine ⟨subset_antisymm ((he p').mpr ⟨Subset.rfl, hd'.symm⟩).1
    ((he p).mp ⟨Subset.rfl, hd.symm⟩).1, ?_⟩
  have sub {a b : Input n} (h : Disjoint a b) : a ⊆ univ \ b :=
    fun i hi => mem_sdiff.mpr ⟨mem_univ _, disjoint_left.mp h hi⟩
  have dd (q : Input n) : Disjoint q (univ \ q) := disjoint_left.mpr (fun _ hi hj => (mem_sdiff.mp hj).2 hi)
  have h₁ := ((he (univ \ q')).mpr ⟨sub hd', dd _⟩).2
  have h₂ := ((he (univ \ q)).mp ⟨sub hd, dd _⟩).2
  have ss {v w : Input n} (h : Disjoint v (univ \ w)) : v ⊆ w := by
    intro i hi
    by_contra hn
    exact disjoint_left.mp h hi (mem_sdiff.mpr ⟨mem_univ _, hn⟩)
  exact subset_antisymm (ss h₁) (ss h₂)

private theorem label_inj {S : Input n} {E : Finset (Edge n)} (ordered : ∀ e ∈ E, e.1 < e.2) :
    Set.InjOn column (codes S E : Set (Label n)) := by
  intro t ht u hu he
  change t ∈ codes S E at ht
  change u ∈ codes S E at hu
  have ⟨hP, hN⟩ := cube_unique (cube_disjoint ordered t ht) (cube_disjoint ordered u hu)
    (fun x => (cube_rep t x).symm.trans ((congrArg (fun f => f x = true) he).to_iff.trans (cube_rep u x)))
  have pairs {i k j l : Fin n} (hik : i < k) (hjl : j < l)
      (hp : ({i,k} : Input n) = {j,l}) : i = j ∧ k = l := by
    have h₁ : i ∈ ({j,l} : Input n) := hp ▸ mem_insert_self _ _
    have h₂ : k ∈ ({j,l} : Input n) := hp ▸ mem_insert_of_mem (mem_singleton_self _)
    simp only [mem_insert, mem_singleton] at h₁ h₂
    rcases h₁ with h | h <;> rcases h₂ with h' | h' <;> first | exact ⟨h,h'⟩ | omega
  cases t with
  | neg i =>
    cases u with
    | neg j => simpa [constraints] using congrArg Label.neg (Finset.singleton_injective hN)
    | low e =>
      have hl := ordered e (codes_low.mp hu)
      dsimp only [constraints] at hN
      have h₁ : e.1 ∈ ({i} : Input n) := hN.symm ▸ mem_insert_self _ _
      have h₂ : e.2 ∈ ({i} : Input n) := hN.symm ▸ mem_insert_of_mem (mem_singleton_self _)
      simp at h₁ h₂
      omega
    | left e => simp [constraints] at hP
    | right e => simp [constraints] at hP
  | low e =>
    cases u with
    | neg i =>
      have hl := ordered e (codes_low.mp ht)
      dsimp only [constraints] at hN
      have h₁ : e.1 ∈ ({i} : Input n) := hN ▸ mem_insert_self _ _
      have h₂ : e.2 ∈ ({i} : Input n) := hN ▸ mem_insert_of_mem (mem_singleton_self _)
      simp at h₁ h₂
      omega
    | low e' => exact congrArg Label.low (Prod.ext (pairs (ordered _ (codes_low.mp ht)) (ordered _ (codes_low.mp hu)) hN).1 (pairs (ordered _ (codes_low.mp ht)) (ordered _ (codes_low.mp hu)) hN).2)
    | left e' => simp [constraints] at hP
    | right e' => simp [constraints] at hP
  | left e =>
    cases u with
    | neg i => simp [constraints] at hP
    | low e' => simp [constraints] at hP
    | left e' => exact congrArg Label.left (Prod.ext (singleton_injective hP) (singleton_injective hN))
    | right e' =>
      have hl := ordered e (codes_left.mp ht)
      have hl' := ordered e' (codes_right.mp hu)
      simp [constraints] at hP hN
      omega
  | right e =>
    cases u with
    | neg i => simp [constraints] at hP
    | low e' => simp [constraints] at hP
    | left e' =>
      have hl := ordered e (codes_right.mp ht)
      have hl' := ordered e' (codes_left.mp hu)
      simp [constraints] at hP hN
      omega
    | right e' => exact congrArg Label.right (Prod.ext (singleton_injective hN) (singleton_injective hP))

private def todo (S : Input n) (E : Finset (Edge n)) := (codes S E).image column
private def inputs (E : Finset (Edge n)) : Finset (Column n) :=
  {fun _ => false,fun _ => true} ∪ univ.image pos ∪ E.image parity ∪ E.image diff

private theorem card_todo {E : Finset (Edge n)} (ordered : ∀ e ∈ E, e.1 < e.2) (S : Input n) :
    (todo S E).card = n + 3*E.card - S.card := by
  classical
  rw [todo, card_image_of_injOn (label_inj ordered)]
  unfold codes
  have ds {U : Finset (Label n)} {f : Edge n → Label n} (sep : ∀ e ∈ E, f e ∉ U) :
      Disjoint U (E.image f) := by
    refine disjoint_right.mpr ?_
    intro t ht
    obtain ⟨e, he, rfl⟩ := mem_image.mp ht
    exact sep e he
  rw [card_union_of_disjoint (ds (by simp)), card_union_of_disjoint (ds (by simp)),
    card_union_of_disjoint (ds (by simp)), card_image_of_injective _ (fun _ _ h => Label.neg.inj h),
    card_image_of_injective _ (fun _ _ h => Label.low.inj h), card_image_of_injective _ (fun _ _ h => Label.left.inj h),
    card_image_of_injective _ (fun _ _ h => Label.right.inj h)]
  have h : S.card ≤ n := by simpa using S.card_le_univ
  simp [card_sdiff_of_subset (Finset.subset_univ S)]
  omega

end

noncomputable section
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {n c : ℕ}

private def res (A : Finset (Input n)) (f : Column n) : A → Bool := fun x => f x
private def sources (E : Finset (Edge n)) (S : Input n) := (inputs E ∪ S.image lit).toList
private def dataL (A : Finset (Input n)) (E : Finset (Edge n)) (S : Input n) :=
  (sources E S).map (res A)
private def targets (A : Finset (Input n)) (E : Finset (Edge n)) := (todo ∅ E).image (res A)
private def hits (a : Fin n → Fin c) (S : Input n) := ∀ j, ∃ i ∈ S, a i = j

private theorem in_L (A : Finset (Input n)) (E : Finset (Edge n)) (S : Input n) (f : Column n)
    (hf : f ∈ inputs E ∨ ∃ i ∈ S, lit i = f) : res A f ∈ dataL A E S := by
  apply List.mem_map.mpr
  exact ⟨f, by simpa [sources] using hf, rfl⟩

private theorem raw_pos (i : Fin n) (E : Finset (Edge n)) : pos i ∈ inputs E := by
  simp [inputs, Finset.mem_image_of_mem pos (mem_univ i)]

private theorem raw_par {e : Edge n} {E : Finset (Edge n)} (he : e ∈ E) : parity e ∈ inputs E := by
  simp [inputs, Finset.mem_image_of_mem parity he]

private theorem raw_diff {e : Edge n} {E : Finset (Edge n)} (he : e ∈ E) : diff e ∈ inputs E := by
  simp [inputs, Finset.mem_image_of_mem diff he]

private theorem in_tgt {E : Finset (Edge n)} (A : Finset (Input n)) (t : Label n)
    (ht : t ∈ codes ∅ E) : res A (column t) ∈ targets A E :=
  mem_image_of_mem _ (mem_image_of_mem _ ht)

private theorem data_pos (A : Finset (Input n)) (E : Finset (Edge n)) (S : Input n) :
    0 < (dataL A E S).length :=
  List.length_pos_of_mem (in_L A E S (fun _ => false) (.inl (by simp [inputs])))

private theorem generable {E : Finset (Edge n)} (a : Fin n → Fin c)
    (conn : ∀ Z : Input n, (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, a i = a j → (i ∈ Z ↔ j ∈ Z))
    (A : Finset (Input n)) (S : Input n)
    (seed : hits a S ∨ ∀ i, res A (lit i) ∈ dataL A E S) :
    derivable (dataL A E S) (targets A E) := by
  classical
  intro U input gate
  have posU (i) := input _ (in_L A E S _ (.inl (raw_pos i E)))
  have make (b : Bool) (f g : Column n) (t : Label n) (ht : t ∈ codes ∅ E)
      (h : ∀ x, mix b f g x = column t x) (hf : res A f ∈ U) (hg : res A g ∈ U) :
      res A (column t) ∈ U := by
    have eq : mix b (res A f) (res A g) = res A (column t) := funext (fun x => h x.val)
    exact eq ▸ gate b _ hf _ hg (eq.symm ▸ in_tgt A t ht)
  have leftU (e) (he : e ∈ E) : res A (column (.left e)) ∈ U := by
    apply make true (pos e.1) (diff e) _ (by simpa using he) _ (posU _) (input _ (in_L A E S _ (.inl (raw_diff he))))
    intro x
    simp only [column, diff, parity, lit, mix, ite_true]
    cases pos e.1 x <;> cases pos e.2 x <;> rfl
  have rightU (e) (he : e ∈ E) : res A (column (.right e)) ∈ U := by
    apply make true (pos e.2) (diff e) _ (by simpa using he) _ (posU _) (input _ (in_L A E S _ (.inl (raw_diff he))))
    intro x
    simp only [column, diff, parity, lit, mix, ite_true]
    cases pos e.1 x <;> cases pos e.2 x <;> rfl
  have low₁ (e) (he : e ∈ E) (h : res A (lit e.1) ∈ U) : res A (column (.low e)) ∈ U := by
    apply make true (lit e.1) (parity e) _ (by simpa using he) _ h (input _ (in_L A E S _ (.inl (raw_par he))))
    intro x
    simp only [column, parity, lit, mix, ite_true]
    cases pos e.1 x <;> cases pos e.2 x <;> rfl
  have low₂ (e) (he : e ∈ E) (h : res A (lit e.2) ∈ U) : res A (column (.low e)) ∈ U := by
    apply make true (lit e.2) (parity e) _ (by simpa using he) _ h (input _ (in_L A E S _ (.inl (raw_par he))))
    intro x
    simp only [column, parity, lit, mix, ite_true]
    cases pos e.1 x <;> cases pos e.2 x <;> rfl
  have allLit (i) : res A (lit i) ∈ U := by
    rcases seed with hit | all
    · let Z := univ.filter (fun k => res A (lit k) ∈ U)
      have hz (k) : k ∈ Z ↔ res A (lit k) ∈ U := by simp [Z]
      have same (e) (he : e ∈ E) : e.1 ∈ Z ↔ e.2 ∈ Z := by
        rw [hz, hz]
        constructor
        · intro h
          apply make false (column (.low e)) (column (.left e)) (.neg e.2) (by simp) _ (low₁ e he h) (leftU e he)
          intro x
          simp only [mix, column, lit]
          cases pos e.1 x <;> cases pos e.2 x <;> rfl
        · intro h
          apply make false (column (.low e)) (column (.right e)) (.neg e.1) (by simp) _ (low₂ e he h) (rightU e he)
          intro x
          simp only [mix, column, lit]
          cases pos e.1 x <;> cases pos e.2 x <;> rfl
      obtain ⟨k, hk, hki⟩ := hit (a i)
      exact (hz i).mp (((conn Z).mp same k i hki).mp ((hz k).mpr (input _ (in_L A E S _ (.inr ⟨k,hk,rfl⟩)))))
    · exact input _ (all i)
  intro f hf
  obtain ⟨_, h, rfl⟩ := mem_image.mp hf
  obtain ⟨t, ht, rfl⟩ := mem_image.mp h
  cases t with
  | neg i => exact allLit i
  | low e => exact low₁ e (codes_low.mp ht) (allLit _)
  | left e => exact leftU e (codes_left.mp ht)
  | right e => exact rightU e (codes_right.mp ht)

private theorem todo_split {E : Finset (Edge n)} (S : Input n) :
    todo ∅ E = todo S E ∪ S.image lit := by
  ext f
  constructor
  · intro hf
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hf
    cases t with
    | neg i =>
      by_cases hi : i ∈ S
      · exact mem_union_right _ (mem_image_of_mem _ hi)
      · exact mem_union_left _ (mem_image_of_mem _ (codes_neg.mpr hi))
    | low e => exact mem_union_left _ (mem_image_of_mem _ (codes_low.mpr (codes_low.mp ht)))
    | left e => exact mem_union_left _ (mem_image_of_mem _ (codes_left.mpr (codes_left.mp ht)))
    | right e => exact mem_union_left _ (mem_image_of_mem _ (codes_right.mpr (codes_right.mp ht)))
  · intro hf
    rcases mem_union.mp hf with h | h
    · obtain ⟨t, ht, rfl⟩ := mem_image.mp h
      apply mem_image_of_mem
      cases t <;> simp_all
    · obtain ⟨i, _, rfl⟩ := mem_image.mp h
      exact mem_image_of_mem column (codes_neg.mpr (notMem_empty i))

private theorem lit_not_todo {E : Finset (Edge n)} (ordered : ∀ e ∈ E, e.1 < e.2)
    {S : Input n} {i} (hi : i ∈ S) : lit i ∉ todo S E := by
  intro h
  obtain ⟨t, ht, he⟩ := mem_image.mp h
  have ht' : t ∈ codes ∅ E := by cases t <;> simp_all
  have eq := label_inj (S := ∅) ordered ht' (codes_neg.mpr (notMem_empty i)) he
  exact codes_neg.mp (eq ▸ ht) hi

private def gap (A : Finset (Input n)) (E : Finset (Edge n)) (S : Input n) :=
  targets A E \ (dataL A E S).toFinset

private theorem gap_subset {A : Finset (Input n)} {E : Finset (Edge n)} {S T : Input n}
    (available : ∀ i ∈ T, res A (lit i) ∈ dataL A E S) :
    gap A E S ⊆ (todo T E).image (res A) := by
  intro f hf
  obtain ⟨hf, hn⟩ := mem_sdiff.mp hf
  obtain ⟨g, hg, rfl⟩ := mem_image.mp hf
  rw [todo_split T] at hg
  rcases mem_union.mp hg with h | h
  · exact mem_image_of_mem _ h
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp h
    exact (hn (List.mem_toFinset.mpr (available i hi))).elim

private theorem gap_eq {A : Finset (Input n)} {E : Finset (Edge n)}
    (ordered : ∀ e ∈ E, e.1 < e.2) (S : Input n) (sep : separated (inputs E) (todo ∅ E) A) :
    (gap A E S).card = n + 3*E.card - S.card := by
  classical
  have part := todo_split (E := E) S
  have inc : todo S E ⊆ todo ∅ E := part ▸ subset_union_left
  have diff' {f g} (hf : f ∈ todo ∅ E) (hg : g ∈ inputs E ∨ (g ∈ todo ∅ E ∧ f ≠ g)) :
      res A f ≠ res A g := by
    obtain ⟨x, hx, hfg⟩ := sep _ _ ⟨hf,hg⟩
    exact fun h => hfg (congrFun h ⟨x,hx⟩)
  have inj : Set.InjOn (res A) (todo S E : Set (Column n)) := by
    intro f hf g hg he
    exact by_contra (fun hn => diff' (inc hf) (.inr ⟨inc hg, hn⟩) he)
  have eq : gap A E S = (todo S E).image (res A) := by
    apply subset_antisymm (gap_subset (fun i hi => in_L A E S _ (.inr ⟨i,hi,rfl⟩)))
    intro f hf
    obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
    refine mem_sdiff.mpr ⟨mem_image_of_mem _ (inc hg), ?_⟩
    intro hL
    obtain ⟨k,hk,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hL)
    have h := mem_union.mp (Finset.mem_toList.mp hk)
    rcases h with h | h
    · exact diff' (inc hg) (.inl h) he.symm
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp h
      have hg' : lit i ∈ todo ∅ E := part ▸ mem_union_right _ (mem_image_of_mem _ hi)
      exact diff' (inc hg) (.inr ⟨hg', fun e => lit_not_todo ordered hi (e ▸ hg)⟩) he.symm
  rw [eq, card_image_of_injOn inj, card_todo ordered]

private def bankKeeps (a : Fin n → Fin c) (E : Finset (Edge n)) (A : Finset (Input n)) :=
  ∀ S p, fits (dataL A E S) (targets A E) p ↔ hits a S ∧ n+3*E.card-S.card ≤ p

private theorem flip_from_keeps {a : Fin n → Fin c} {E : Finset (Edge n)}
    (conn : ∀ Z : Input n, (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, a i = a j → (i ∈ Z ↔ j ∈ Z))
    {A : Finset (Input n)} (hk : bankKeeps a E A) : hasFlips a A := by
  classical
  intro j
  by_contra! noflip
  let S := univ \ fiber a j
  have anti (x y : A) (h : ∀ f ∈ dataL A E S, f x = true → f y = true) : x = y := by
    have xy : x.val ⊆ y.val := by
      intro i hi
      simpa [res, pos] using h _ (in_L A E S _ (.inl (raw_pos i E))) (by simpa [res, pos] using hi)
    let Z := y.val \ x.val
    have hz (i) : i ∈ Z ↔ i ∈ y.val ∧ i ∉ x.val := mem_sdiff
    have edge (e) (he : e ∈ E) : e.1 ∈ Z ↔ e.2 ∈ Z := by
      have hp := h _ (in_L A E S _ (.inl (raw_par he)))
      have hd := h _ (in_L A E S _ (.inl (raw_diff he)))
      have hu := @xy e.1
      have hv := @xy e.2
      dsimp only [res, diff, parity, pos] at hp hd
      rw [hz, hz]
      by_cases h₁ : e.1 ∈ x.val <;> by_cases h₂ : e.1 ∈ y.val <;>
        by_cases h₃ : e.2 ∈ x.val <;> by_cases h₄ : e.2 ∈ y.val <;> simp_all
    have outside (i) (hi : i ∈ Z) : a i = j := by
      by_contra hn
      have hs : i ∈ S := by simp [S, hn]
      have hh := h _ (in_L A E S _ (.inr ⟨i,hs,rfl⟩))
      obtain ⟨hiy,hix⟩ := (hz i).mp hi
      simp [res, lit, pos, hix, hiy] at hh
    by_contra hne
    have missing : ∃ i ∈ y.val, i ∉ x.val := by
      by_contra! hall
      exact hne (Subtype.ext (subset_antisymm xy hall))
    obtain ⟨i, hiy, hix⟩ := missing
    have hi := (hz i).mpr ⟨hiy,hix⟩
    have eq : Z = fiber a j := by
      ext k
      rw [mem_fiber]
      exact ⟨outside k, fun hc => ((conn Z).mp edge i k ((outside i hi).trans hc.symm)).mp hi⟩
    have dis : Disjoint x.val (fiber a j) := by
      rw [← eq]
      exact disjoint_left.mpr (fun k hk hZ => ((hz k).mp hZ).2 hk)
    have un : x.val ∪ fiber a j = y.val := by
      rw [← eq]
      ext k
      simp only [mem_union, hz]
      exact ⟨fun h => h.elim (fun hk => xy hk) And.left,
        fun hk => or_iff_not_imp_left.mpr (fun hn => ⟨hk,hn⟩)⟩
    exact noflip _ x.property dis (un ▸ y.property)
  obtain ⟨p,C,hm,hb,ho,hs,hall⟩ := fits_all (dataL A E S)
    (in_L A E S _ (.inl (by simp [inputs] : (fun _ => false) ∈ inputs E)))
    (in_L A E S _ (.inl (by simp [inputs] : (fun _ => true) ∈ inputs E))) anti
  have good : fits (dataL A E S) (targets A E) p :=
    ⟨C,hm,hb,ho,hs,fun f _ => hall f (mem_univ _)⟩
  obtain ⟨i,hi,hij⟩ := ((hk S p).mp good).1 j
  simp [S, hij] at hi

private theorem hits_from_flips {a : Fin n → Fin c} (sur : Function.Surjective a) {E : Finset (Edge n)}
    (conn : ∀ Z : Input n, (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, a i = a j → (i ∈ Z ↔ j ∈ Z))
    {A : Finset (Input n)} (hp : hasFlips a A) {S p} (good : fits (dataL A E S) (targets A E) p) :
    hits a S := by
  classical
  intro j
  by_contra! miss
  obtain ⟨x,hx,hd,ht⟩ := hp j
  let y := x ∪ fiber a j
  have low (i) (hi : a i = j) : i ∉ x := fun h => disjoint_left.mp hd h (mem_fiber.mpr hi)
  have high (i) (hi : a i = j) : i ∈ y := mem_union_right _ (mem_fiber.mpr hi)
  have unchanged (i) (hi : a i ≠ j) : pos i y = pos i x := by simp [pos,y,hi]
  have par (e) (he : e ∈ E) : parity e x = parity e y := by
    have same := (conn (fiber a j)).mpr (fun i k h => by simp only [mem_fiber]; rw [h]) e he
    simp only [mem_fiber] at same
    by_cases h : a e.1 = j
    · have hh := same.mp h
      simp [parity, pos, low _ h, low _ hh, high _ h, high _ hh]
    · simp [parity, unchanged _ h, unchanged _ (same.not.mp h)]
  let X : A := ⟨x,hx⟩
  let Y : A := ⟨y,ht⟩
  have ordered (f) (hf : f ∈ dataL A E S) : f X = true → f Y = true := by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    change g x = true → g y = true
    simp only [sources, Finset.mem_toList, inputs, mem_union, mem_insert, mem_singleton, mem_image,
      mem_univ, true_and] at hg
    rcases hg with (((((rfl | rfl) | ⟨i,rfl⟩) | ⟨e,he,rfl⟩) | ⟨e,he,rfl⟩) | ⟨i,hi,rfl⟩)
    · exact id
    · exact id
    · simpa [pos, y] using fun h : i ∈ x => Or.inl (b := a i = j) h
    · rw [par e he]; exact id
    · simp only [diff, par e he, imp_self]
    · simp only [lit, unchanged _ (miss i hi), imp_self]
  obtain ⟨i, hi⟩ := sur j
  have h := wires_monotone good ordered _ (in_tgt A (.neg i) (by simp))
  simp [X, Y, res, column, lit, pos, low i hi, high i hi] at h

private theorem sep_from_keeps {a : Fin n → Fin c} {E : Finset (Edge n)}
    (ordered : ∀ e ∈ E, e.1 < e.2)
    (conn : ∀ Z : Input n, (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, a i = a j → (i ∈ Z ↔ j ∈ Z))
    {A : Finset (Input n)} (hk : bankKeeps a E A) :
    separated (inputs E) (todo ∅ E) A := by
  classical
  let allSeeds : Input n := univ
  let edges := todo allSeeds E
  have budget (S : Input n) (hall : ∀ i, res A (lit i) ∈ dataL A E S) :
      n+3*E.card-S.card ≤ (gap A E S).card :=
    ((hk S _).mp (synthesize _ (data_pos A E S) _ (generable a conn A S (.inr hall)))).2
  have available (i : Fin n) := in_L A E allSeeds _ (.inr ⟨i,mem_univ _,rfl⟩)
  have enough := budget allSeeds available
  have ec : edges.card = n+3*E.card-allSeeds.card := card_todo ordered _
  have sub : gap A E allSeeds ⊆ edges.image (res A) := gap_subset (fun i _ => available i)
  have equal : gap A E allSeeds = edges.image (res A) :=
    eq_of_subset_of_card_le sub (card_image_le.trans (ec.symm ▸ enough))
  have inj : Set.InjOn (res A) (edges : Set (Column n)) := card_image_iff.mp
    (le_antisymm card_image_le (by rw [← equal, ec]; exact enough))
  have off (f) (hf : f ∈ edges) : res A f ∉ dataL A E allSeeds := by
    have h := mem_image_of_mem (res A) hf
    rw [← equal] at h
    exact fun hL => (mem_sdiff.mp h).2 (List.mem_toFinset.mpr hL)
  have literal (i : Fin n) :
      res A (lit i) ∉ dataL A E (univ.erase i) := by
    let S := (univ : Input n).erase i
    intro hi
    have all (k : Fin n) : res A (lit k) ∈ dataL A E S := by
      by_cases he : k = i
      · exact he ▸ hi
      · exact in_L A E S _ (.inr ⟨k,by simp [S, he],rfl⟩)
    have ub : (gap A E S).card ≤ edges.card :=
      (card_le_card (gap_subset (T := allSeeds) (fun k _ => all k))).trans card_image_le
    have le := (budget S all).trans ub
    have sc : S.card + 1 = n := by simpa [S] using card_erase_add_one (s := (univ : Input n)) (mem_univ i)
    have ac : allSeeds.card = n := by simp [allSeeds]
    omega
  have split (f) (hf : f ∈ todo ∅ E) : f ∈ edges ∨ ∃ i, lit i = f := by
    rw [todo_split (E := E) allSeeds] at hf
    simpa [allSeeds, edges] using hf
  intro f g hfg
  obtain ⟨hf,hg⟩ := hfg
  by_contra! no
  have eq : res A f = res A g := funext (fun x => no x.val x.property)
  rcases split f hf with fe | ⟨i,rfl⟩
  · rcases hg with gr | ⟨gn,ne⟩
    · exact off f fe (eq ▸ in_L A E allSeeds _ (.inl gr))
    · rcases split g gn with ge | ⟨k,rfl⟩
      · exact ne (inj fe ge eq)
      · exact off f fe (eq ▸ available k)
  · rcases hg with gr | ⟨gn,ne⟩
    · exact literal i (eq ▸ in_L A E _ _ (.inl gr))
    · rcases split g gn with ge | ⟨k,rfl⟩
      · exact off _ ge (eq.symm ▸ available i)
      · have hi : k ≠ i := fun h => ne (h ▸ rfl)
        exact literal i (eq ▸ in_L A E _ _ (.inr ⟨k,by simp [hi],rfl⟩))

private theorem bank_criterion {a : Fin n → Fin c} (sur : Function.Surjective a) {E : Finset (Edge n)}
    (ordered : ∀ e ∈ E, e.1 < e.2)
    (conn : ∀ Z : Input n, (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
      ∀ i j, a i = a j → (i ∈ Z ↔ j ∈ Z))
    (A : Finset (Input n)) :
    bankKeeps a E A ↔ separated (inputs E) (todo ∅ E) A ∧ hasFlips a A := by
  refine ⟨fun hk => ⟨sep_from_keeps ordered conn hk, flip_from_keeps conn hk⟩, ?_⟩
  rintro ⟨sep,flips⟩ S p
  have size := gap_eq ordered S sep
  constructor
  · intro good
    have bound : (gap A E S).card ≤ p := wires_needed _ _ good
    exact ⟨hits_from_flips sur conn flips good, size ▸ bound⟩
  · rintro ⟨hit,le⟩
    obtain ⟨C,hm,hb,ho,hc,rep⟩ := synthesize _ (data_pos A E S) _ (generable a conn A S (.inl hit))
    have le' : (gap A E S).card ≤ p := size.symm ▸ le
    exact ⟨C,hm,hb,ho,hc.trans le',rep⟩

private theorem fits_rows (L : List (Column n)) (D : Finset (Column n)) (p : ℕ) (A : Finset (Input n)) :
    fits (L.map (res A)) (D.image (res A)) p ↔
    ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack L.length C ∧
      C.output < L.length + C.size ∧ C.size ≤ p ∧ ∀ f ∈ D, ∃ j < L.length + C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x := by
  simp only [fits, List.length_map, forall_mem_image, funext_iff, wire, res, List.map_map,
    Function.comp_def, Subtype.forall]

private theorem todo_empty (E : Finset (Edge n)) :
    todo ∅ E = univ.image lit ∪ E.image (fun e x => lit e.1 x && lit e.2 x) ∪
      E.image (fun e x => pos e.1 x && lit e.2 x) ∪ E.image (fun e x => lit e.1 x && pos e.2 x) := by
  simp [todo, codes, image_union, image_image, Function.comp_def, column]

end

end PEqualNP.Outside.L_meta_53215

open PEqualNP.Outside.L_meta_53215
theorem PEqualNP.Outside.L_meta_53215 : (∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
  (∀ e ∈ E, e.1 < e.2) → Function.Surjective color →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔
    ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)) →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    (∀ j, ∃ i ∈ S, color i = j) ∧ n+3*E.card-S.card ≤ p
  let comp := fun j : Fin c => Finset.univ.filter (fun i : Fin n => color i = j)
  let norm := fun x : W => x.filter (fun i => ¬ comp (color i) ⊆ x)
  let flips := fun B : Finset W => ∀ j, ∃ x ∈ B, Disjoint x (comp j) ∧ x ∪ comp j ∈ B
  let delta := fun (f : W → Bool) (j : Fin c) =>
    ((f (comp j)).toNat : Int) - ((f ∅).toNat : Int)
  let admissible := fun P : Finset W => P.image norm = P ∧
    (∀ j, ∃ z ∈ P, Disjoint z (comp j)) ∧
    ∀ f ∈ need, ∀ g : W → Bool, (g ∈ raw ∨ (g ∈ need ∧ f ≠ g)) →
      delta f = delta g → ∃ z ∈ P, f z ≠ g z
  (∀ A : Finset W, keeps A ↔ admissible (A.image norm) ∧ flips A) ∧
  (∀ (P : Finset W) (b : Nat),
    (∃ A : Finset W, A.image norm = P ∧ keeps A ∧ A.card ≤ b) ↔
      admissible P ∧ c+P.card ≤ b) ∧
  ∀ P : Finset W, admissible P → ∀ s : Fin c → W,
    (∀ j, s j ∈ P ∧ Disjoint (s j) (comp j)) →
    let B := P ∪ Finset.univ.image (fun j => s j ∪ comp j)
    B.image norm = P ∧ keeps B ∧ B.card = c+P.card) := by
  classical
  intro n c E color hord hsur hconn W bit neg same raw need keeps comp norm flips delta admissible
  have hbit : bit = pos := by
    funext i x
    dsimp only [bit, pos]
    congr!
  have hneg : neg = lit := by
    funext i x
    simp [neg, lit, hbit]
  have hsame : same = parity := by
    funext e x
    dsimp only [same, parity]
    rw [hbit]
    congr!
  have hraw : raw = inputs E := by
    dsimp only [raw,inputs,diff]
    rw [hbit, hsame]
    congr!
  have hneed : need = todo ∅ E := by
    rw [todo_empty]
    dsimp only [need]
    rw [hbit,hneg]
    congr!
  have hk (A) : keeps A ↔ bankKeeps color E A := by
    dsimp only [keeps, bankKeeps]
    apply forall_congr'
    intro S
    apply forall_congr'
    intro p
    unfold dataL targets
    rw [fits_rows, hraw, hneg, hneed]
    dsimp only [sources, hits]
    congr!
  have hfiber : comp = fiber color := by
    funext j
    ext i
    simp [comp]
  have hnorm : norm = normal color := by
    funext x
    ext i
    simp [norm, hfiber]
  have hflips : flips = hasFlips color := by
    funext A
    dsimp only [flips, hasFlips]
    rw [hfiber]
    congr!
  have hdelta : delta = changeAt color := by
    funext f j
    simp [delta, hfiber, changeAt, val]
  have hadm : admissible = adm color raw need := by
    funext P
    dsimp only [admissible, adm]
    rw [hnorm, hfiber, hdelta]
    congr!
  have hbank (A) : keeps A ↔ separated raw need A ∧ hasFlips color A := by
    rw [hk,hraw,hneed]
    exact bank_criterion hsur hord hconn A
  have hreg : ∀ f ∈ raw ∪ need, regular color f := by
    convert graph_regular E color hconn using 1
    congr!
  rw [hadm, hflips, hnorm, hfiber]
  convert from_bank hsur hreg keeps hbank using 1
  congr!
  dsimp only
  congr!
