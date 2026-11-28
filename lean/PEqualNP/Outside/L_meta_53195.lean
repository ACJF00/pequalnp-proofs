import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.Helpers.GraphSeedSamples
import PEqualNP.Library.Helpers.GraphPriceCalibration

-- Credit: the sample lemmas below (shrinkRows through exactColumns) are copied from
-- L_meta_53188 by shubing-joe (Apache-2.0), merged as PR 56932.

namespace PEqualNP.Outside.L_meta_53195

open Classical

private theorem shrinkRows {Row Key : Type} {colors : Nat} (rows : Finset Row)
    (key : Row → Key) (mark : Row → Finset (Fin colors))
    (switch : ∀ color, ∃ x ∈ rows, ∃ y ∈ rows, key x = key y ∧ color ∉ mark x ∧
      mark y = insert color (mark x)) : (rows.image key).card + colors ≤ rows.card := by
  classical
  let view := fun (seen : Finset (Fin colors)) (x : Row) => (key x, mark x ∩ seen)
  have bound (seen : Finset (Fin colors)) : (rows.image key).card + seen.card ≤ (rows.image (view seen)).card := by
    induction seen using Finset.induction_on with
    | empty =>
      have h := Finset.card_image_le (s := rows.image (view ∅)) (f := Prod.fst)
      simpa [Finset.image_image, Function.comp_def, view] using h
    | @insert color seen fresh ih =>
      obtain ⟨x, hx, y, hy, same, absent, add⟩ := switch color
      let cut := fun p : Key × Finset (Fin colors) => (p.1, p.2 ∩ seen)
      let next := rows.image (view (insert color seen))
      have image : next.image cut = rows.image (view seen) := by
        rw [Finset.image_image]
        congr 1
        funext z
        refine Prod.ext (by rfl) ?_
        ext j
        simp [cut, view]
      have drop : (next.image cut).card < next.card := by
        apply lt_of_le_of_ne Finset.card_image_le
        intro heq
        have inj := Finset.card_image_iff.mp heq
        have ceq : cut (view (insert color seen) x) = cut (view (insert color seen) y) := by
          apply Prod.ext same
          ext j
          by_cases h : j = color <;> simp_all [cut, view]
        have eq := inj (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy) ceq
        have diff := congrArg (fun p : Key × Finset (Fin colors) => color ∈ p.2) eq
        simp [view, absent, add] at diff
      rw [image] at drop
      dsimp only [next] at drop
      rw [Finset.card_insert_of_notMem fresh]
      omega
  have h := bound Finset.univ
  simpa using h.trans Finset.card_image_le

open PEqualNP.FiniteGateBank PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def goodNet {width : Nat} (net : Net width) (cost : net.cost = 0) :
    Monotone2 ⟨net.gates, 0⟩ := by
  intro gate hg
  obtain ⟨ops, fan⟩ := net.fan gate hg
  simp only [Net.cost, PEqualNP.NotBracket.notCount, List.length_eq_zero_iff, List.filter_eq_nil_iff] at cost
  have noNot : gate.op ≠ .not := by
    intro h
    simpa [h] using cost gate hg
  exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff, noNot] using ops, fan⟩

private def inputRows {X : Type} (inputs : List (X → Bool)) (x : X) := inputs.map (fun f => f x)

private theorem initHas {X : Type} {inputs : List (X → Bool)} {f : X → Bool} (h : f ∈ inputs) :
    (empty inputs.length).has (inputRows inputs) f := by
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem h
  refine ⟨i, by simpa [empty] using hi, fun x => ?_⟩
  change (inputs.map (fun g => g x)).getD i false = _
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hi, eq]

private theorem allTerms {X J : Type} {w : Nat} {raw : X → List Bool} (width : ∀ x, (raw x).length=w)
    (p : Net w) (one : p.has raw (fun _ => true)) (l : List J) (f : J → X → Bool)
    (known : ∀ i ∈ l, p.has raw (f i)) :
    ∃ q, Grow raw p q l.length 0 ∧ q.has raw (fun x => l.all (fun j => f j x)) := by
  induction l with
  | nil => exact ⟨p, start _ _, one⟩
  | cons j l ih =>
    obtain ⟨q,gq,old⟩ := ih (fun i hi => known i (by simp [hi]))
    obtain ⟨r,gr,ans⟩ := binary width q _ _ (gq.1 _ (known j (by simp))) old true
    exact ⟨r,chain gq gr,by simpa [List.all_cons] using ans⟩

private theorem interpolate {X : Type} [Fintype X] (inputs : List (X → Bool)) (goals : Finset (X → Bool))
    (zero : (fun _ => false) ∈ inputs) (one : (fun _ => true) ∈ inputs)
    (mono : ∀ x y, (∀ f ∈ inputs, f x = true → f y = true) → ∀ g ∈ goals, g x = true → g y = true) :
    ∃ p : Net inputs.length, p.cost = 0 ∧ ∀ f ∈ goals, p.has (inputRows inputs) f := by
  classical
  let raw := inputRows inputs
  let startNet := empty inputs.length
  have width (x) : (raw x).length = inputs.length := by simp [raw, inputRows]
  let conjunction := fun row y => (inputs.filter (fun f => f row)).all (fun f => f y)
  obtain ⟨net, grow, reaches⟩ := batch (raw := raw) startNet goals.toList id
    (Fintype.card X * inputs.length + Fintype.card X) 0 (by
      intro target ht p preserve
      let positives := (Finset.univ.filter (fun row => target row = true)).toList
      obtain ⟨q, growQ, terms⟩ := batch (raw := raw) p positives conjunction inputs.length 0 (by
        intro x hx q lifted
        obtain ⟨r, gr, attained⟩ := allTerms width q (lifted _ (preserve _ (initHas one)))
          (inputs.filter (fun f => f x)) id (fun f hf => lifted _ (preserve _ (initHas (List.mem_filter.mp hf).1)))
        exact ⟨r, allowance gr (List.length_filter_le ..), attained⟩)
      obtain ⟨r, growR, attained⟩ := anyList width q (growQ.1 _ (preserve _ (initHas zero))) positives conjunction terms
      have lengthBound : positives.length ≤ Fintype.card X := by simp [positives, Finset.card_le_univ]
      refine ⟨r, ?_, ?_⟩
      · have step := chain growQ growR
        simp only [Nat.mul_zero, Nat.add_zero] at step
        exact allowance step (Nat.add_le_add (Nat.mul_le_mul_right _ lengthBound) lengthBound)
      · convert attained using 2 with y
        apply Bool.eq_iff_iff.mpr
        simp only [id_eq, List.any_eq_true, conjunction, List.all_eq_true, List.mem_filter,
          positives, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hy
          exact ⟨y, hy, fun _ h => h.2⟩
        · rintro ⟨x,hx,step⟩
          exact mono x y (fun f hf h => step f ⟨hf,h⟩) target (Finset.mem_toList.mp ht) hx)
  exact ⟨net, by simpa [startNet, empty, Net.cost, PEqualNP.NotBracket.notCount] using grow.2.2,
    fun f hf => reaches f (Finset.mem_toList.mpr hf)⟩

private abbrev Row (n : Nat) := Finset (Fin n)
private abbrev Edges (n : Nat) := Finset (Fin n × Fin n)
private noncomputable def bit {n} (i : Fin n) (x : Row n) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  decide (i ∈ x)
private noncomputable def neg {n} (i : Fin n) (x : Row n) := !(bit i x)
private noncomputable def same {n} (e : Fin n × Fin n) (x : Row n) := bit e.1 x == bit e.2 x
private noncomputable def low {n} (e : Fin n × Fin n) (x : Row n) := neg e.1 x && neg e.2 x
private noncomputable def forward {n} (e : Fin n × Fin n) (x : Row n) := bit e.1 x && neg e.2 x
private noncomputable def backward {n} (e : Fin n × Fin n) (x : Row n) := neg e.1 x && bit e.2 x
private noncomputable def raw {n} (edges : Edges n) : Finset (Row n → Bool) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪ edges.image same ∪ edges.image (fun e x => !(same e x))
private noncomputable def need {n} (edges : Edges n) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  Finset.univ.image neg ∪ edges.image low ∪ edges.image forward ∪ edges.image backward
private noncomputable def seeds {n} (edges : Edges n) (s : Row n) :=
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  (raw edges ∪ s.image neg).toList
private def Can {X : Type} (rows : Finset X) (inputs : List (X → Bool)) (goals : Finset (X → Bool)) (budget : Nat) :=
  ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack inputs.length C ∧ C.output < inputs.length+C.size ∧
    C.size ≤ budget ∧ ∀ f ∈ goals, ∃ j < inputs.length+C.size, ∀ x ∈ rows, (C.wires (inputs.map (fun g => g x))).getD j false = f x

private def Keeps {n c} (edges : Edges n) (color : Fin n → Fin c) (rows : Finset (Row n)) :=
  ∀ s p, Can rows (seeds edges s) (need edges) p ↔ (∀ j, ∃ i ∈ s, color i = j) ∧ n+3*edges.card-s.card ≤ p

private def restrictF {X : Type} (rows : Finset X) (f : X → Bool) (x : ↥rows) := f x.val

private theorem fromNet {X : Type} {rows : Finset X} {inputs : List (X → Bool)} {goals : Finset (X → Bool)}
    {p : Net ((inputs.map (restrictF rows)).length)} (hn : p.cost = 0) (nonempty : inputs ≠ [])
    (achieves : ∀ f ∈ goals, p.has (inputRows (inputs.map (restrictF rows))) (restrictF rows f)) :
    Can rows inputs goals p.gates.length := by
  refine ⟨⟨p.gates,0⟩, goodNet p hn, ?_, ?_, le_rfl, ?_⟩
  · simpa using p.readsBack
  · have := List.length_pos_iff.mpr nonempty
    change 0 < inputs.length + p.gates.length
    omega
  · intro f hf
    obtain ⟨j,hj,he⟩ := achieves f hf
    refine ⟨j,by simpa [Circuit.size] using hj,fun x hx => ?_⟩
    simpa [inputRows, restrictF, List.map_map, Function.comp_def, Circuit.wires, CoverCircuit.run] using he ⟨x,hx⟩

private theorem forbiddenPair {X : Type} (rows : Finset X) (inputs : List (X → Bool)) (goals : Finset (X → Bool))
    (zero : (fun _ => false) ∈ inputs) (one : (fun _ => true) ∈ inputs)
    (impossible : ∀ budget, ¬Can rows inputs goals budget) :
    ∃ x ∈ rows, ∃ y ∈ rows, x ≠ y ∧ ∀ f ∈ inputs, f x = true → f y = true := by
  classical
  by_contra! h
  let restricted := inputs.map (restrictF rows)
  have monotone (x y : ↥rows) (ord : ∀ f ∈ restricted, f x = true → f y = true) : x = y := by
    by_contra neq
    obtain ⟨f,hf,hx,hy⟩ := h x x.property y y.property (fun eq => neq (Subtype.ext eq))
    have lift := ord _ (List.mem_map.mpr ⟨f,hf,rfl⟩) hx
    exact hy lift
  obtain ⟨p,hp,has⟩ := interpolate restricted (goals.image (restrictF rows))
    (List.mem_map.mpr ⟨_,zero,rfl⟩) (List.mem_map.mpr ⟨_,one,rfl⟩) (by
      intro x y ord f hf hx
      exact monotone x y ord ▸ hx)
  exact impossible _ (fromNet hp (fun eq => by simp [eq] at one) (fun f hf => has _ (Finset.mem_image_of_mem _ hf)))

private def Connect {n c} (E : Edges n) (color : Fin n → Fin c) :=
  ∀ Z : Row n, (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) ↔ ∀ i j, color i = color j → (i ∈ Z ↔ j ∈ Z)

private theorem edgeColor {n c} {E : Edges n} {color : Fin n → Fin c} (h : Connect E color)
    {e} (he : e ∈ E) : color e.1 = color e.2 := by
  let fiber := Finset.univ.filter (fun i => color i = color e.1)
  have constant : ∀ i j, color i = color j → (i ∈ fiber ↔ j ∈ fiber) := by intro i j eq; simp [fiber,eq]
  have := ((h fiber).mpr constant e he).mp (by simp [fiber])
  simpa [fiber, eq_comm] using this

private theorem seedRaw {n} {E : Edges n} {s : Row n} {f} (h : f ∈ raw E) : f ∈ seeds E s := by
  simp [seeds,h]

private theorem switchPair {n c} {E : Edges n} {color : Fin n → Fin c} {A : Finset (Row n)}
    (components : Connect E color) (keeps : Keeps E color A) (j : Fin c) :
    ∃ x ∈ A, ∃ y ∈ A, (∀ i, color i = j → i ∉ x ∧ i ∈ y) ∧ (∀ i, color i ≠ j → (i ∈ x ↔ i ∈ y)) := by
  classical
  let s := Finset.univ.filter (fun i => color i ≠ j)
  obtain ⟨x,hx,y,hy,neq,ord⟩ := forbiddenPair A (seeds E s) (need E)
    (seedRaw (by simp [raw])) (seedRaw (by simp [raw])) (by
      intro budget hc
      obtain ⟨i,hi,eq⟩ := ((keeps s budget).mp hc).1 j
      simpa [s, eq] using hi)
  have sub (i) (h : i ∈ x) : i ∈ y := by
    have hw := ord (bit i) (seedRaw (by simp [raw, Finset.mem_image_of_mem])) (by simpa [bit] using h)
    simpa [bit] using hw
  have outside (i) (hj : color i ≠ j) : i ∈ x ↔ i ∈ y := by
    refine ⟨sub i, fun hi => ?_⟩
    by_contra hn
    have hw := ord (neg i) (by simp only [seeds,Finset.mem_toList,Finset.mem_union,Finset.mem_image]; exact Or.inr ⟨i,by simp [s,hj],rfl⟩) (by simp [neg, bit, hn])
    simp [neg,bit,hi] at hw
  have equalEdge (e) (he : e ∈ E) : same e x = same e y := by
    have hpos := ord (same e) (seedRaw (by simp only [raw,Finset.mem_union,Finset.mem_image]; exact Or.inl (Or.inr ⟨e,he,rfl⟩)))
    have hneg := ord (fun z => !(same e z)) (seedRaw (by simp only [raw,Finset.mem_union,Finset.mem_image]; exact Or.inr ⟨e,he,rfl⟩))
    cases h1 : same e x <;> cases h2 : same e y <;> simp_all
  have closed : ∀ e ∈ E, e.1 ∈ y \ x ↔ e.2 ∈ y \ x := by
    intro e he
    have eq := equalEdge e he
    have h1 := sub e.1
    have h2 := sub e.2
    by_cases a : e.1 ∈ x <;> by_cases b : e.1 ∈ y <;> by_cases d : e.2 ∈ x <;> by_cases k : e.2 ∈ y <;>
      simp_all [same,bit]
  obtain ⟨v,hv⟩ : (y \ x).Nonempty := by
    by_contra! empty
    apply neq
    ext i
    specialize sub i
    have := Finset.ext_iff.mp empty i
    simp at this
    exact ⟨sub,this⟩
  have changed := Finset.mem_sdiff.mp hv
  have target : color v = j := by by_contra hn; exact changed.2 ((outside v hn).mpr changed.1)
  refine ⟨x,hx,y,hy,?_,outside⟩
  intro i hi
  exact (Finset.mem_sdiff.mp (((components _).mp closed v i (target.trans hi.symm)).mp hv)).symm

private abbrev Arrows {n} (E : Edges n) := ↥E × Bool
private abbrev Tags {n} (E : Edges n) := Sum (↥E) (Arrows E)
private noncomputable def atom {n} {E : Edges n} (d : Arrows E) :=
  if d.2 then forward d.1.val else backward d.1.val
private noncomputable def signal {n} {E : Edges n} (t : Tags E) :=
  Sum.elim (fun e : ↥E => low e.val) atom t

private theorem exactColumns {n c} {E : Edges n} {color : Fin n → Fin c} {A : Finset (Row n)}
    (keeps : Keeps E color A) : Function.Injective (fun d : Arrows E => restrictF A (atom d)) ∧
    ∀ d : Arrows E, restrictF A (atom d) ≠ fun _ => false := by
  classical
  let inputs := seeds E Finset.univ
  let L := inputs.map (restrictF A)
  let rawIn := inputRows L
  let col := fun t : Tags E => restrictF A (signal t)
  let full := Finset.univ.image col
  let zero : ↥A → Bool := fun _ => false
  let pool := full.erase zero
  let init := empty L.length
  have rawHas (f : Row n → Bool) (hf : f ∈ inputs) : init.has rawIn (restrictF A f) :=
    initHas (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have rawBit (i : Fin n) := rawHas (bit i) (seedRaw (by simp [raw,Finset.mem_image_of_mem]))
  have rawNeg (i : Fin n) := rawHas (neg i) (by simp [inputs,seeds])
  have rawZero : init.has rawIn zero := rawHas (fun _ => false) (seedRaw (by simp [raw]))
  have nonempty : inputs ≠ [] := by
    have hz : (fun _ => false) ∈ inputs := seedRaw (by simp [raw])
    intro eq; simp [eq] at hz
  obtain ⟨p,grows,has⟩ := batch (raw := rawIn) init pool.toList id 1 0 (by
    intro f hf q ext
    have member := Finset.mem_of_mem_erase (Finset.mem_toList.mp hf)
    obtain ⟨tag,_,rfl⟩ := Finset.mem_image.mp member
    have width (x) : (rawIn x).length = L.length := by simp [rawIn,inputRows]
    cases tag with
    | inl e => exact binary width q _ _ (ext _ (rawNeg e.val.1)) (ext _ (rawNeg e.val.2)) true
    | inr d =>
      rcases d with ⟨e,b⟩
      cases b
      · exact binary width q _ _ (ext _ (rawNeg e.val.1)) (ext _ (rawBit e.val.2)) true
      · exact binary width q _ _ (ext _ (rawBit e.val.1)) (ext _ (rawNeg e.val.2)) true)
  have allTags (t : Tags E) : p.has rawIn (col t) := by
    by_cases h : col t = zero
    · exact h ▸ grows.1 _ rawZero
    · exact has _ (Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨h,Finset.mem_image_of_mem _ (Finset.mem_univ t)⟩))
  have built : Can A inputs (need E) p.gates.length := by
    refine fromNet (by simpa [init, empty, Net.cost, PEqualNP.NotBracket.notCount] using grows.2.2) nonempty ?_
    intro f hf
    simp only [need,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hf
    rcases hf with (((⟨i,rfl⟩ | ⟨e,he,rfl⟩) | ⟨e,he,rfl⟩) | ⟨e,he,rfl⟩)
    · exact grows.1 _ (rawNeg i)
    · exact allTags (.inl ⟨e,he⟩)
    · exact allTags (.inr (⟨e,he⟩, true))
    · exact allTags (.inr (⟨e,he⟩, false))
  have minSize := ((keeps Finset.univ _).mp built).2
  have upper := grows.2.1
  simp [init,empty] at upper
  simp only [Finset.card_univ,Fintype.card_fin] at minSize
  have ht : Fintype.card (Tags E) = 3 * E.card := by simp [Tags,Arrows]; omega
  have imageBound : full.card ≤ Fintype.card (Tags E) := Finset.card_image_le.trans_eq Finset.card_univ
  have eraseBound : pool.card ≤ full.card := Finset.card_le_card (Finset.erase_subset ..)
  have fullSize : full.card = (Finset.univ : Finset (Tags E)).card := by rw [Finset.card_univ]; omega
  have inject := Finset.card_image_iff.mp fullSize
  refine ⟨fun d e h => Sum.inr.inj (inject (x₁ := Sum.inr d) (x₂ := Sum.inr e) (Finset.mem_univ _) (Finset.mem_univ _) h), ?_⟩
  intro d hz
  have hz' : zero ∈ full := Finset.mem_image.mpr ⟨Sum.inr d,Finset.mem_univ _,hz⟩
  have drop : pool.card < full.card := Finset.card_erase_lt_of_mem hz'
  omega

private theorem collapseRows {n c} {E : Edges n} {color : Fin n → Fin c} {A : Finset (Row n)}
    (onto : Function.Surjective color) (components : Connect E color) (keeps : Keeps E color A) :
    (A.image (fun (x : Row n) (d : Arrows E) => atom d x)).card + c ≤ A.card := by
  classical
  let key := fun (x : Row n) (d : Arrows E) => atom d x
  let mark := fun (x : Row n) => Finset.univ.filter (fun j => (onto j).choose ∈ x)
  have collapse := shrinkRows A key mark (by
    intro j
    obtain ⟨x,hx,y,hy,flip,stable⟩ := switchPair components keeps j
    refine ⟨x,hx,y,hy,?_,?_,?_⟩
    · funext d
      rcases d with ⟨e,b⟩
      have sameColor := edgeColor components e.property
      by_cases h : color e.val.1 = j
      · obtain ⟨a,aa⟩ := flip _ h
        obtain ⟨b',bb⟩ := flip _ (sameColor.symm.trans h)
        cases b <;> simp [key,atom,forward,backward,bit,neg,a,aa,b',bb]
      · have a := stable _ h
        have b' := stable _ (fun eq => h (sameColor.trans eq))
        cases b <;> simp [key,atom,forward,backward,bit,neg,a,b'] <;> congr!
    · simp [mark,(flip _ (onto j).choose_spec).1]
    · ext k
      by_cases eq : k = j
      · subst k; simp [mark,(flip _ (onto j).choose_spec).2]
      · have stableRep := stable _ (fun h => eq ((onto k).choose_spec.symm.trans h))
        simp [mark,eq,stableRep])
  convert collapse using 0 <;> congr!

private noncomputable def sideFlag {n} (v : Fin n) (b : Bool) (e : Fin n × Fin n) : Bool :=
  if b then decide (e.1 = v) else !decide (e.1 = v)

private theorem sideValue {n} {E : Edges n} {v : Fin n} {b : Bool} {e : Fin n × Fin n} (he : e ∈ E)
    (hv : e.1 = v ∨ e.2 = v) (x : Row n) (h : atom ((⟨e,he⟩ : ↥E), sideFlag v b e) x = true) :
    (v ∈ x ↔ b = true) := by
  by_cases h1 : e.1 = v
  · subst v
    cases b <;> simp_all [atom, sideFlag, forward, backward, bit, neg]
  · have h2 : e.2 = v := hv.resolve_left h1
    subst v
    cases b <;> simp_all [atom, sideFlag, forward, backward, bit, neg]

private theorem starBound {n c} {E : Edges n} {color : Fin n → Fin c} {A : Finset (Row n)}
    (onto : Function.Surjective color) (components : Connect E color) (keeps : Keeps E color A)
    (v : Fin n) (h : Nat) (deg : 2^(h-1) ≤ (E.filter (fun e => e.1 = v ∨ e.2 = v)).card) :
    c + 1 + 2*h ≤ A.card := by
  classical
  have reduced := collapseRows onto components keeps
  let key := fun (x : Row n) (d : Arrows E) => atom d x
  let P := A.image key
  change P.card + c ≤ A.card at reduced
  let D := E.filter (fun e => e.1 = v ∨ e.2 = v)
  let side := fun (b : Bool) (e : Fin n × Fin n) =>
    P.filter (fun p => ∃ he : e ∈ E, p (⟨e,he⟩, sideFlag v b e) = true)
  let Q := fun b : Bool => P.filter (fun p => ∃ e ∈ D, ∃ he : e ∈ E, p (⟨e,he⟩, sideFlag v b e) = true)
  obtain ⟨different, used⟩ := exactColumns keeps
  have memSide (b : Bool) (e) (he : e ∈ E) (x) (hx : x ∈ A) :
      key x ∈ side b e ↔ atom ((⟨e,he⟩ : ↥E), sideFlag v b e) x = true := by
    simp only [side, Finset.mem_filter]
    exact ⟨fun hh => hh.2.elim (fun _ hh' => hh'), fun hh => ⟨Finset.mem_image_of_mem _ hx, he, hh⟩⟩
  have count (b : Bool) : h ≤ (Q b).card := by
    have le : D.card ≤ ((Q b).powerset.erase ∅).card := by
      apply Finset.card_le_card_of_injOn (side b)
      · intro e heD
        have he : e ∈ E := (Finset.mem_filter.mp heD).1
        show side b e ∈ (Q b).powerset.erase ∅
        rw [Finset.mem_erase, Finset.mem_powerset]
        refine ⟨?_, ?_⟩
        · obtain ⟨x, hx⟩ : ∃ x : ↥A, atom ((⟨e,he⟩ : ↥E), sideFlag v b e) x.val = true := by
            by_contra! none
            apply used (⟨e,he⟩, sideFlag v b e)
            funext x
            simpa [restrictF] using none x
          intro hempty
          have := (memSide b e he x.val x.property).mpr hx
          rw [hempty] at this
          simp at this
        · intro p hp
          simp only [side, Finset.mem_filter] at hp
          exact Finset.mem_filter.mpr ⟨hp.1, e, heD, hp.2⟩
      · intro e heD e' heD' eq
        have he : e ∈ E := (Finset.mem_filter.mp heD).1
        have he' : e' ∈ E := (Finset.mem_filter.mp heD').1
        have cols := different (a₁ := ((⟨e,he⟩ : ↥E), sideFlag v b e)) (a₂ := ((⟨e',he'⟩ : ↥E), sideFlag v b e')) (by
          funext x
          apply Bool.eq_iff_iff.mpr
          show atom _ x.val = true ↔ atom _ x.val = true
          rw [← memSide b e he x.val x.property, ← memSide b e' he' x.val x.property, eq])
        exact congrArg (fun d : Arrows E => d.1.val) cols
    have cardErase : ((Q b).powerset.erase ∅).card = 2^(Q b).card - 1 := by
      rw [Finset.card_erase_of_mem (Finset.empty_mem_powerset _), Finset.card_powerset]
    have pos : 0 < 2^(Q b).card := pow_pos (by norm_num) _
    have lt : 2^(h-1) < 2^(Q b).card := by
      change 2^(h-1) ≤ D.card at deg
      omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp lt
    omega
  have disj : Disjoint (Q true) (Q false) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨hpP, e, heD, he, h1⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, e', heD', he', h2⟩ := Finset.mem_filter.mp hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hpP
    have a := sideValue he (Finset.mem_filter.mp heD).2 x h1
    have b := sideValue he' (Finset.mem_filter.mp heD').2 x h2
    simp at a b
    exact b a
  obtain ⟨x, hx, _, _, flip, _⟩ := switchPair components keeps (color v)
  have zero : key x ∈ P \ (Q true ∪ Q false) := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ hx, ?_⟩
    intro hm
    have hm' : ∃ b, key x ∈ Q b := by
      rcases Finset.mem_union.mp hm with hm | hm
      · exact ⟨_, hm⟩
      · exact ⟨_, hm⟩
    obtain ⟨b, hb⟩ := hm'
    obtain ⟨_, e, heD, he, h1⟩ := Finset.mem_filter.mp hb
    have hv := (Finset.mem_filter.mp heD).2
    have c12 := edgeColor components he
    have c1 : color e.1 = color v := by
      rcases hv with hv | hv
      · rw [hv]
      · rw [c12, hv]
    have n1 := (flip e.1 c1).1
    have n2 := (flip e.2 (c12.symm.trans c1)).1
    change atom ((⟨e,he⟩ : ↥E), sideFlag v b e) x = true at h1
    cases hb : sideFlag v b e <;> simp_all [atom, forward, backward, bit, neg]
  have sub : Q true ∪ Q false ⊆ P := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp <;> exact (Finset.mem_filter.mp hp).1
  have big : (Q true ∪ Q false).card < P.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨sub, ?_⟩
    intro eq
    have := Finset.mem_sdiff.mp zero
    rw [eq] at this
    exact this.2 this.1
  rw [Finset.card_union_of_disjoint disj] at big
  have := count true
  have := count false
  omega

private abbrev RowIx (c q h : Nat) := Option (Fin c ⊕ (Fin q ⊕ (Fin h ⊕ Fin h)))

private noncomputable def rowVal {n c q h : Nat} (color : Fin n → Fin c) (center : Fin c → Fin n)
    (group : Fin c → Fin (2^q)) (word : Fin n → Finset (Fin h)) : RowIx c q h → Fin n → Bool
  | none => fun _ => false
  | some (Sum.inl j) => fun i => decide (color i = j)
  | some (Sum.inr (Sum.inl t)) => fun i =>
      if center (color i) = i then (group (color i)).val.testBit t.val else !(group (color i)).val.testBit t.val
  | some (Sum.inr (Sum.inr (Sum.inl k))) => fun i => if center (color i) = i then false else decide (k ∈ word i)
  | some (Sum.inr (Sum.inr (Sum.inr k))) => fun i => if center (color i) = i then true else decide (k ∉ word i)

private def GoodW {n c q h : Nat} (color : Fin n → Fin c) (center : Fin c → Fin n)
    (group : Fin c → Fin (2^q)) (word : Fin n → Finset (Fin h)) : Prop :=
  (∀ j, color (center j) = j) ∧ (∀ i, center (color i) ≠ i → (word i).Nonempty) ∧
  (∀ i i', center (color i) ≠ i → center (color i') ≠ i' → group (color i) = group (color i') →
    word i = word i' → i = i')

private abbrev Fn (n : Nat) := (Fin n → Bool) → Bool

private def kindF {n c : Nat} (color : Fin n → Fin c) (center : Fin c → Fin n) (k : Fin 3) (u : Fin n) : Fn n :=
  fun v => if k = 0 then !(v (center (color u))) && !(v u)
    else if k = 1 then v (center (color u)) && !(v u) else !(v (center (color u))) && v u

private def famF {n c : Nat} (color : Fin n → Fin c) (center : Fin c → Fin n) : Fin n ⊕ (Fin n × Fin 3) → Fn n
  | Sum.inl i => fun v => !(v i)
  | Sum.inr p => kindF color center p.2 p.1

private def validT {n c : Nat} (color : Fin n → Fin c) (center : Fin c → Fin n) : Fin n ⊕ (Fin n × Fin 3) → Prop
  | Sum.inl _ => True
  | Sum.inr p => center (color p.1) ≠ p.1

private theorem tagInj {q : Nat} {g g' : Fin (2^q)} (h : ∀ t : Fin q, g.val.testBit t.val = g'.val.testBit t.val) :
    g = g' := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < q
  · exact h ⟨i, hi⟩
  · have hq : 2^q ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le g.isLt hq), Nat.testBit_eq_false_of_lt (lt_of_lt_of_le g'.isLt hq)]

private theorem wordExt {h : Nat} {a b : Finset (Fin h)} (H : ∀ k, decide (k ∈ a) = decide (k ∈ b)) : a = b := by
  ext k
  simpa using H k

section frame
variable {n c q h : Nat} {color : Fin n → Fin c} {center : Fin c → Fin n}
  {group : Fin c → Fin (2^q)} {word : Fin n → Finset (Fin h)}

private theorem profileInj (G : GoodW color center group word) {i i' : Fin n}
    (H : ∀ r, rowVal color center group word r i = rowVal color center group word r i') : i = i' := by
  obtain ⟨hcen, wne, winj⟩ := G
  have col : color i = color i' := by
    have := H (some (Sum.inl (color i)))
    simp [rowVal] at this
    first | exact this | exact this.symm
  by_cases ci : center (color i) = i <;> by_cases ci' : center (color i') = i'
  · rw [← ci, ← ci', col]
  · obtain ⟨k, hk⟩ := wne i' ci'
    have := H (some (Sum.inr (Sum.inr (Sum.inl k))))
    simp [rowVal, ci, ci', hk] at this
  · obtain ⟨k, hk⟩ := wne i ci
    have := H (some (Sum.inr (Sum.inr (Sum.inl k))))
    simp [rowVal, ci, ci', hk] at this
  · apply winj i i' ci ci' (by rw [col])
    apply wordExt
    intro k
    have := H (some (Sum.inr (Sum.inr (Sum.inl k))))
    simpa [rowVal, ci, ci'] using this

private theorem famInj (G : GoodW color center group word) (a b : Fin n ⊕ (Fin n × Fin 3))
    (va : validT color center a) (vb : validT color center b)
    (H : ∀ r, famF color center a (rowVal color center group word r) = famF color center b (rowVal color center group word r)) :
    a = b := by
  have G' := G
  obtain ⟨hcen, wne, winj⟩ := G'
  rcases a with i | ⟨u, k⟩ <;> rcases b with i' | ⟨u', k'⟩
  · congr 1
    apply profileInj G
    intro r
    have := H r
    simpa [famF] using this
  · exfalso
    simp only [validT] at vb
    have z := H none
    fin_cases k'
    · by_cases ci : center (color i) = i
      · obtain ⟨k, hk⟩ := wne u' vb
        have := H (some (Sum.inr (Sum.inr (Sum.inl k))))
        simp [famF, kindF, rowVal, ci, vb, hk, hcen] at this
      · obtain ⟨k, hk⟩ := wne i ci
        have := H (some (Sum.inr (Sum.inr (Sum.inr k))))
        simp [famF, kindF, rowVal, ci, vb, hk, hcen] at this
    · simp [famF, kindF, rowVal] at z
    · simp [famF, kindF, rowVal] at z
  · exfalso
    simp only [validT] at va
    have z := H none
    fin_cases k
    · by_cases ci : center (color i') = i'
      · obtain ⟨k, hk⟩ := wne u va
        have := H (some (Sum.inr (Sum.inr (Sum.inl k))))
        simp [famF, kindF, rowVal, ci, va, hk, hcen] at this
      · obtain ⟨k, hk⟩ := wne i' ci
        have := H (some (Sum.inr (Sum.inr (Sum.inr k))))
        simp [famF, kindF, rowVal, ci, va, hk, hcen] at this
    · simp [famF, kindF, rowVal] at z
    · simp [famF, kindF, rowVal] at z
  · simp only [validT] at va vb
    have z := H none
    have sameLeaf (gr : group (color u) = group (color u'))
        (w : ∀ k, decide (k ∈ word u) = decide (k ∈ word u')) : u = u' :=
      winj u u' va vb gr (wordExt w)
    have tagged (s : Bool) (ht : ∀ t : Fin q, (if s then (group (color u)).val.testBit t.val else !(group (color u)).val.testBit t.val) =
        (if s then (group (color u')).val.testBit t.val else !(group (color u')).val.testBit t.val)) :
        group (color u) = group (color u') := by
      apply tagInj
      intro t
      have := ht t
      cases s <;> simpa using this
    fin_cases k <;> fin_cases k'
    · have col : color u = color u' := by
        have := H (some (Sum.inl (color u)))
        simp [famF, kindF, rowVal, va, vb, hcen] at this
        first | exact this | exact this.symm
      have := sameLeaf (by rw [col]) (by
        intro k
        have := H (some (Sum.inr (Sum.inr (Sum.inl k))))
        simpa [famF, kindF, rowVal, va, vb, hcen] using this)
      subst this; rfl
    · simp [famF, kindF, rowVal, va, vb, hcen] at z
    · simp [famF, kindF, rowVal, va, vb, hcen] at z
    · simp [famF, kindF, rowVal, va, vb, hcen] at z
    · have gr := tagged true (by
        intro t
        have := H (some (Sum.inr (Sum.inl t)))
        simpa [famF, kindF, rowVal, va, vb, hcen] using this)
      have := sameLeaf gr (by
        intro k
        have := H (some (Sum.inr (Sum.inr (Sum.inr k))))
        simpa [famF, kindF, rowVal, va, vb, hcen] using this)
      subst this; rfl
    · obtain ⟨k, hk⟩ := wne u' vb
      have := H (some (Sum.inr (Sum.inr (Sum.inl k))))
      simp [famF, kindF, rowVal, va, vb, hcen, hk] at this
    · simp [famF, kindF, rowVal, va, vb, hcen] at z
    · obtain ⟨k, hk⟩ := wne u va
      have := H (some (Sum.inr (Sum.inr (Sum.inl k))))
      simp [famF, kindF, rowVal, va, vb, hcen, hk] at this
    · have gr := tagged false (by
        intro t
        have := H (some (Sum.inr (Sum.inl t)))
        simpa [famF, kindF, rowVal, va, vb, hcen] using this)
      have := sameLeaf gr (by
        intro k
        have := H (some (Sum.inr (Sum.inr (Sum.inl k))))
        simpa [famF, kindF, rowVal, va, vb, hcen] using this)
      subst this; rfl

end frame

section frame2
variable {n c q h : Nat} {color : Fin n → Fin c} {center : Fin c → Fin n}
  {group : Fin c → Fin (2^q)} {word : Fin n → Finset (Fin h)}

private theorem rawAway (G : GoodW color center group word) (a : Fin n ⊕ (Fin n × Fin 3))
    (va : validT color center a) (ρ : Fn n)
    (hρ : ρ = (fun _ => false) ∨ ρ = (fun _ => true) ∨ (∃ j, ρ = fun v => v j) ∨
      (∃ u, center (color u) ≠ u ∧ (ρ = (fun v => v (center (color u)) == v u) ∨
        ρ = (fun v => v u == v (center (color u))) ∨ ρ = (fun v => xor (v (center (color u))) (v u)) ∨
        ρ = (fun v => xor (v u) (v (center (color u)))))))
    (H : ∀ r, famF color center a (rowVal color center group word r) = ρ (rowVal color center group word r)) : False := by
  obtain ⟨hcen, wne, winj⟩ := G
  have z := H none
  rcases a with i | ⟨u, k⟩
  · have s := H (some (Sum.inl (color i)))
    rcases hρ with rfl | rfl | ⟨j, rfl⟩ | ⟨u', hu', rfl | rfl | rfl | rfl⟩ <;>
      simp [famF, rowVal, hcen] at z s
  · simp only [validT] at va
    have s := H (some (Sum.inl (color u)))
    obtain ⟨w, hw⟩ := wne u va
    have b1 := H (some (Sum.inr (Sum.inr (Sum.inl w))))
    have b2 := H (some (Sum.inr (Sum.inr (Sum.inr w))))
    fin_cases k
    · rcases hρ with rfl | rfl | ⟨j, rfl⟩ | ⟨u', hu', rfl | rfl | rfl | rfl⟩ <;>
        simp [famF, kindF, rowVal, hcen, va] at z s
    · rcases hρ with rfl | rfl | ⟨j, rfl⟩ | ⟨u', hu', rfl | rfl | rfl | rfl⟩
      · simp [famF, kindF, rowVal, hcen, va, hw] at b2
      · simp [famF, kindF, rowVal, hcen, va] at z
      · have sj := H (some (Sum.inl (color j)))
        simp [famF, kindF, rowVal, hcen, va] at sj
      · simp [famF, kindF, rowVal, hcen, va, hu'] at z
      · simp [famF, kindF, rowVal, hcen, va, hu'] at z
      · obtain ⟨w', hw'⟩ := wne u' hu'
        have b := H (some (Sum.inr (Sum.inr (Sum.inl w'))))
        simp [famF, kindF, rowVal, hcen, va, hu', hw'] at b
      · obtain ⟨w', hw'⟩ := wne u' hu'
        have b := H (some (Sum.inr (Sum.inr (Sum.inl w'))))
        simp [famF, kindF, rowVal, hcen, va, hu', hw'] at b
    · rcases hρ with rfl | rfl | ⟨j, rfl⟩ | ⟨u', hu', rfl | rfl | rfl | rfl⟩
      · simp [famF, kindF, rowVal, hcen, va, hw] at b1
      · simp [famF, kindF, rowVal, hcen, va] at z
      · have sj := H (some (Sum.inl (color j)))
        simp [famF, kindF, rowVal, hcen, va] at sj
      · simp [famF, kindF, rowVal, hcen, va, hu'] at z
      · simp [famF, kindF, rowVal, hcen, va, hu'] at z
      · obtain ⟨w', hw'⟩ := wne u' hu'
        have b := H (some (Sum.inr (Sum.inr (Sum.inr w'))))
        simp [famF, kindF, rowVal, hcen, va, hu', hw'] at b
      · obtain ⟨w', hw'⟩ := wne u' hu'
        have b := H (some (Sum.inr (Sum.inr (Sum.inr w'))))
        simp [famF, kindF, rowVal, hcen, va, hu', hw'] at b

end frame2

private noncomputable def leafOf {n c : Nat} (color : Fin n → Fin c) (center : Fin c → Fin n) (e : Fin n × Fin n) : Fin n :=
  if center (color e.1) = e.1 then e.2 else e.1

private theorem leafForm {n c : Nat} {E : Edges n} {color : Fin n → Fin c} {center : Fin c → Fin n}
    (sorted : ∀ e ∈ E, e.1 < e.2) (components : Connect E color) (hcen : ∀ j, color (center j) = j)
    (hstar : ∀ e ∈ E, e.1 = center (color e.1) ∨ e.2 = center (color e.1)) {e : Fin n × Fin n} (he : e ∈ E) :
    center (color (leafOf color center e)) ≠ leafOf color center e ∧
      (e = (center (color (leafOf color center e)), leafOf color center e) ∨
        e = (leafOf color center e, center (color (leafOf color center e)))) := by
  have col := edgeColor components he
  have lt := sorted e he
  unfold leafOf
  by_cases h1 : center (color e.1) = e.1
  · rw [if_pos h1, ← col, h1]
    exact ⟨ne_of_lt lt, Or.inl rfl⟩
  · rw [if_neg h1]
    refine ⟨h1, Or.inr ?_⟩
    rcases hstar e he with h | h
    · exact absurd h.symm h1
    · rw [← h]

private theorem leafInj {n c : Nat} {E : Edges n} {color : Fin n → Fin c} {center : Fin c → Fin n}
    (sorted : ∀ e ∈ E, e.1 < e.2) (components : Connect E color) (hcen : ∀ j, color (center j) = j)
    (hstar : ∀ e ∈ E, e.1 = center (color e.1) ∨ e.2 = center (color e.1)) {e e' : Fin n × Fin n}
    (he : e ∈ E) (he' : e' ∈ E) (eq : leafOf color center e = leafOf color center e') : e = e' := by
  have f := (leafForm sorted components hcen hstar he).2
  have f' := (leafForm sorted components hcen hstar he').2
  rw [← eq] at f'
  have lt := sorted e he
  have lt' := sorted e' he'
  rcases f with f | f <;> rcases f' with f' | f'
  · rw [f, f']
  · rw [f'] at lt'; rw [f] at lt; exact absurd (lt.trans lt') (lt_irrefl _)
  · rw [f'] at lt'; rw [f] at lt; exact absurd (lt.trans lt') (lt_irrefl _)
  · rw [f, f']

private theorem leafEdge {n c : Nat} {E : Edges n} {color : Fin n → Fin c} {center : Fin c → Fin n}
    (components : Connect E color) (hcen : ∀ j, color (center j) = j)
    (hstar : ∀ e ∈ E, e.1 = center (color e.1) ∨ e.2 = center (color e.1)) (i : Fin n)
    (hi : center (color i) ≠ i) : ∃ e ∈ E, leafOf color center e = i := by
  by_contra! none
  have away : ∀ e ∈ E, e.1 ≠ i ∧ e.2 ≠ i := by
    intro e he
    have col := edgeColor components he
    constructor
    · intro h1
      apply none e he
      unfold leafOf
      rw [if_neg (by rw [h1]; exact hi), h1]
    · intro h2
      rcases hstar e he with h | h
      · apply none e he
        unfold leafOf
        rw [if_pos h.symm, h2]
      · apply hi
        rw [← h2, ← col, ← h]
  have closed : ∀ e ∈ E, e.1 ∈ ({i} : Finset (Fin n)) ↔ e.2 ∈ ({i} : Finset (Fin n)) := by
    intro e he
    simp [(away e he).1, (away e he).2]
  have := ((components {i}).mp closed (center (color i)) i (hcen _)).mpr (by simp)
  exact hi (by simpa using this)

private theorem wordsExist {n c q h : Nat} {E : Edges n} {color : Fin n → Fin c} {center : Fin c → Fin n}
    {group : Fin c → Fin (2^q)}
    (sorted : ∀ e ∈ E, e.1 < e.2) (components : Connect E color) (hcen : ∀ j, color (center j) = j)
    (hstar : ∀ e ∈ E, e.1 = center (color e.1) ∨ e.2 = center (color e.1))
    (hgroup : ∀ j, (E.filter (fun e => group (color e.1) = j)).card < 2^h) :
    ∃ word : Fin n → Finset (Fin h), (∀ i, center (color i) ≠ i → (word i).Nonempty) ∧
      (∀ i i', center (color i) ≠ i → center (color i') ≠ i' → group (color i) = group (color i') →
        word i = word i' → i = i') := by
  classical
  let leaves := fun g : Fin (2^q) => Finset.univ.filter (fun i => center (color i) ≠ i ∧ group (color i) = g)
  have few (g) : (leaves g).card < 2^h := by
    refine lt_of_le_of_lt ?_ (hgroup g)
    refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := E.filter (fun e => group (color e.1) = g)) (f := leafOf color center))
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    obtain ⟨e, he, rfl⟩ := leafEdge components hcen hstar i hi'.1
    refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, rfl⟩
    have col := edgeColor components he
    have : color (leafOf color center e) = color e.1 := by
      unfold leafOf
      split <;> simp [col]
    rw [← this]
    exact hi'.2
  have emb (g) : Nonempty (↥(leaves g) ↪ ↥((Finset.univ : Finset (Finset (Fin h))).erase ∅)) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_coe]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    have := few g
    omega
  let ε := fun g => Classical.choice (emb g)
  let wordOf := fun (g : Fin (2^q)) (i : Fin n) => if hi : i ∈ leaves g then ((ε g) ⟨i,hi⟩).val else ∅
  have mem (i) (hi : center (color i) ≠ i) : i ∈ leaves (group (color i)) := by simp [leaves, hi]
  refine ⟨fun i => wordOf (group (color i)) i, ?_, ?_⟩
  · intro i hi
    simp only [wordOf, dif_pos (mem i hi)]
    apply Finset.nonempty_iff_ne_empty.mpr
    exact Finset.ne_of_mem_erase ((ε (group (color i))) ⟨i, mem i hi⟩).property
  · intro i i' hi hi' gr heq
    have hm' := mem i' hi'
    rw [← gr] at hm'
    change wordOf (group (color i)) i = wordOf (group (color i')) i' at heq
    rw [← gr] at heq
    simp only [wordOf, dif_pos (mem i hi), dif_pos hm'] at heq
    have := (ε (group (color i))).injective (Subtype.ext heq)
    exact congrArg Subtype.val this

private theorem priceExact {n c q h m : Nat} {E : Edges n} {color : Fin n → Fin c} {center : Fin c → Fin n}
    {group : Fin c → Fin (2^q)} {word : Fin n → Finset (Fin h)} (G : GoodW color center group word)
    (sorted : ∀ e ∈ E, e.1 < e.2) (components : Connect E color)
    (hstar : ∀ e ∈ E, e.1 = center (color e.1) ∨ e.2 = center (color e.1))
    (eqv : RowIx c q h ≃ Fin m) (x : Fin m → Fin n → Bool)
    (hx : ∀ k, x k = rowVal color center group word (eqv.symm k)) (S : Finset (Fin n)) :
    let project := fun (f : Fn n) (k : Fin m) => f (x k)
    let raw : Finset (Fn n) := {fun _ => false,fun _ => true} ∪ Finset.univ.image (fun i v => v i) ∪
      E.image (fun e v => v e.1 == v e.2) ∪ E.image (fun e v => xor (v e.1) (v e.2))
    let targets : Finset (Fn n) := Finset.univ.image (fun (i : Fin n) (v : Fin n → Bool) => !(v i)) ∪
      E.image (fun e v => !(v e.1) && !(v e.2)) ∪
      E.image (fun e v => v e.1 && !(v e.2)) ∪ E.image (fun e v => !(v e.1) && v e.2)
    ((targets.image project) \ (raw.image project ∪ S.image (fun i => project (fun v => !(v i))))).card =
      n + 3*E.card - S.card := by
  intro project raw targets
  have hcen := G.1
  let ι' : Fin n ⊕ (↥E × Fin 3) → Fin n ⊕ (Fin n × Fin 3) :=
    Sum.map id (fun p => (leafOf color center p.1.val, p.2))
  let TR := fun t => project (famF color center (ι' t))
  have vt : ∀ t, validT color center (ι' t) := by
    rintro (i | ⟨⟨e, he⟩, k⟩)
    · trivial
    · exact (leafForm sorted components hcen hstar he).1
  have back : ∀ f g : Fn n, project f = project g → ∀ r, f (rowVal color center group word r) = g (rowVal color center group word r) := by
    intro f g hfg r
    have := congrFun hfg (eqv r)
    simpa [project, hx] using this
  have inj : Function.Injective TR := by
    intro t t' heq
    have := famInj G _ _ (vt t) (vt t') (back _ _ heq)
    rcases t with i | ⟨⟨e, he⟩, k⟩ <;> rcases t' with i' | ⟨⟨e', he'⟩, k'⟩ <;> simp [ι'] at this ⊢
    · exact this
    · exact ⟨leafInj sorted components hcen hstar he he' this.1, this.2⟩
  have sub : Finset.univ.image TR ⊆ targets.image project := by
    intro τ hτ
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hτ
    apply Finset.mem_image_of_mem
    rcases t with i | ⟨⟨e, he⟩, k⟩
    · apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · obtain ⟨-, form⟩ := leafForm sorted components hcen hstar he
      change kindF color center k (leafOf color center e) ∈ targets
      generalize leafOf color center e = u at form ⊢
      rcases form with rfl | rfl
      · fin_cases k
        · apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_right
          refine Finset.mem_image.mpr ⟨_, he, ?_⟩
          funext v; cases h1 : v (center (color u)) <;> cases h2 : v u <;> simp [kindF, h1, h2]
        · apply Finset.mem_union_left; apply Finset.mem_union_right
          refine Finset.mem_image.mpr ⟨_, he, ?_⟩
          funext v; cases h1 : v (center (color u)) <;> cases h2 : v u <;> simp [kindF, h1, h2]
        · apply Finset.mem_union_right
          refine Finset.mem_image.mpr ⟨_, he, ?_⟩
          funext v; cases h1 : v (center (color u)) <;> cases h2 : v u <;> simp [kindF, h1, h2]
      · fin_cases k
        · apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_right
          refine Finset.mem_image.mpr ⟨_, he, ?_⟩
          funext v; cases h1 : v (center (color u)) <;> cases h2 : v u <;> simp [kindF, h1, h2]
        · apply Finset.mem_union_right
          refine Finset.mem_image.mpr ⟨_, he, ?_⟩
          funext v; cases h1 : v (center (color u)) <;> cases h2 : v u <;> simp [kindF, h1, h2]
        · apply Finset.mem_union_left; apply Finset.mem_union_right
          refine Finset.mem_image.mpr ⟨_, he, ?_⟩
          funext v; cases h1 : v (center (color u)) <;> cases h2 : v u <;> simp [kindF, h1, h2]
  have cardU : (Finset.univ.image TR).card = n + 3*E.card := by
    rw [Finset.card_image_of_injective _ inj, Finset.card_univ]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    ring
  have cardT : (targets.image project).card ≤ n + 3*E.card := by
    refine Finset.card_image_le.trans ?_
    refine ((Finset.card_union_le _ _).trans (add_le_add ((Finset.card_union_le _ _).trans
      (add_le_add ((Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le))
        Finset.card_image_le)) Finset.card_image_le)).trans ?_
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hD : targets.image project = Finset.univ.image TR :=
    (Finset.eq_of_subset_of_card_le sub (by omega)).symm
  have away : ∀ t, TR t ∉ raw.image project := by
    intro t hm
    obtain ⟨ρ, hρ, heq⟩ := Finset.mem_image.mp hm
    apply rawAway G (ι' t) (vt t) ρ ?_ (fun r => back _ _ heq.symm r)
    simp only [raw, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_univ, true_and] at hρ
    rcases hρ with (((h0 | h1) | ⟨j, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))
    · obtain ⟨hu, form⟩ := leafForm sorted components hcen hstar he
      generalize leafOf color center e = u at form hu
      rcases form with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr ⟨u, hu, Or.inl rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨u, hu, Or.inr (Or.inl rfl)⟩))
    · obtain ⟨hu, form⟩ := leafForm sorted components hcen hstar he
      generalize leafOf color center e = u at form hu
      rcases form with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr ⟨u, hu, Or.inr (Or.inr (Or.inl rfl))⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨u, hu, Or.inr (Or.inr (Or.inr rfl))⟩))
  let N := S.image (fun i => project (fun v => !(v i)))
  have hN : N ⊆ Finset.univ.image TR := by
    intro τ hτ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hτ
    exact Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, rfl⟩
  have cardN : N.card = S.card :=
    Finset.card_image_of_injective S (fun i i' hii => Sum.inl_injective (inj (a₁ := Sum.inl i) (a₂ := Sum.inl i') hii))
  have split : Finset.univ.image TR \ (raw.image project ∪ N) = Finset.univ.image TR \ N := by
    ext τ
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
    constructor
    · exact fun hh => ⟨hh.1, hh.2.2⟩
    · intro hh
      refine ⟨hh.1, ?_, hh.2⟩
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hh.1
      exact away t
  change (targets.image project \ (raw.image project ∪ N)).card = _
  rw [hD, split]
  have := Finset.card_sdiff_add_card_eq_card hN
  omega

private noncomputable def asRow {n : Nat} (v : Fin n → Bool) : Row n := Finset.univ.filter (fun i => v i = true)

private theorem bitAsRow {n : Nat} (i : Fin n) (v : Fin n → Bool) : bit i (asRow v) = v i := by
  cases hv : v i <;> simp [bit, asRow, hv]

private theorem rawLift {n : Nat} (E : Edges n) :
    (raw E).image (fun g (v : Fin n → Bool) => g (asRow v)) =
      {fun _ => false,fun _ => true} ∪ Finset.univ.image (fun i (v : Fin n → Bool) => v i) ∪
      E.image (fun e (v : Fin n → Bool) => v e.1 == v e.2) ∪ E.image (fun e (v : Fin n → Bool) => xor (v e.1) (v e.2)) := by
  have hx : ∀ a b : Bool, (!(a == b)) = xor a b := by decide
  simp only [raw, Finset.image_union, Finset.image_insert, Finset.image_singleton, Finset.image_image,
    Function.comp_def, same, bitAsRow, hx]

private theorem needLift {n : Nat} (E : Edges n) :
    (need E).image (fun g (v : Fin n → Bool) => g (asRow v)) =
      Finset.univ.image (fun (i : Fin n) (v : Fin n → Bool) => !(v i)) ∪
      E.image (fun e (v : Fin n → Bool) => !(v e.1) && !(v e.2)) ∪
      E.image (fun e (v : Fin n → Bool) => v e.1 && !(v e.2)) ∪ E.image (fun e (v : Fin n → Bool) => !(v e.1) && v e.2) := by
  simp only [need, Finset.image_union, Finset.image_image, Function.comp_def, low, forward, backward, neg, bitAsRow]

private theorem upperBuild {n c : Nat} {E : Edges n} {color : Fin n → Fin c}
    (sorted : ∀ e ∈ E, e.1 < e.2) (components : Connect E color)
    (center : Fin c → Fin n) (h q : Nat) (group : Fin c → Fin (2^q))
    (hcen : ∀ j, color (center j) = j)
    (hstar : ∀ e ∈ E, e.1 = center (color e.1) ∨ e.2 = center (color e.1))
    (hgroup : ∀ j, (E.filter (fun e => group (color e.1) = j)).card < 2^h) :
    ∃ A : Finset (Row n), Keeps E color A ∧ A.card ≤ c+1+q+2*h := by
  classical
  obtain ⟨word, wne, winj⟩ := wordsExist (group := group) sorted components hcen hstar hgroup
  have G : GoodW color center group word := ⟨hcen, wne, winj⟩
  let m := Fintype.card (RowIx c q h)
  let eqv : RowIx c q h ≃ Fin m := Fintype.equivFin (RowIx c q h)
  let x : Fin m → Fin n → Bool := fun k => rowVal color center group word (eqv.symm k)
  let A : Finset (Row n) := Finset.univ.image (fun k => asRow (x k))
  refine ⟨A, ?_, ?_⟩
  swap
  · refine Finset.card_image_le.trans ?_
    simp only [Finset.card_univ, Fintype.card_fin, m, RowIx, Fintype.card_option, Fintype.card_sum]
    omega
  have pairs : ∀ j, ∃ a b, (∀ i, color i = j → x a i = false ∧ x b i = true) ∧
      (∀ i, color i ≠ j → x a i = x b i) := by
    intro j
    refine ⟨eqv none, eqv (some (Sum.inl j)), ?_, ?_⟩ <;> intro i hi <;> simp [x, rowVal, hi]
  let K := Finset.univ.image center
  have one : ∀ j, ∃! i, i ∈ K ∧ color i = j := by
    intro j
    refine ⟨center j, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hcen j⟩, ?_⟩
    rintro i ⟨hi, rfl⟩
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hi
    rw [hcen]
  have cr := PEqualNP.GraphPriceCalibration.criterion n m c E color x sorted components pairs K one
  let P := fun (g : Row n → Bool) (k : Fin m) => g (asRow (x k))
  let inputs := fun S : Finset (Fin n) => (seeds E S).map P
  have hin : ∀ S, (inputs S).toFinset = (({fun _ => false,fun _ => true} : Finset (Fn n)) ∪
      Finset.univ.image (fun i (v : Fin n → Bool) => v i) ∪
      E.image (fun e (v : Fin n → Bool) => v e.1 == v e.2) ∪
      E.image (fun e (v : Fin n → Bool) => xor (v e.1) (v e.2))).image (fun f k => f (x k)) ∪
      S.image (fun i => (fun f k => f (x k)) (fun (v : Fin n → Bool) => !(v i))) := by
    intro S
    have tf : ∀ l : List (Row n → Bool), (l.map P).toFinset = l.toFinset.image P := by
      intro l
      ext τ
      simp
    simp only [inputs, tf, seeds, Finset.toList_toFinset, Finset.image_union, ← rawLift,
      Finset.image_image, Function.comp_def, P, neg, bitAsRow]
  have cr' := cr inputs hin
  dsimp only at cr'
  have fit := cr'.1
  intro S p
  have cost := priceExact G sorted components hstar eqv x (fun _ => rfl) S
  dsimp only at cost
  have f := fit S p
  rw [cost] at f
  refine Iff.trans ?_ f
  rw [← needLift E]
  simp only [Can, inputs, P, A, List.length_map, List.map_map, Finset.image_image, Function.comp_def,
    Finset.forall_mem_image, Finset.mem_univ, true_implies, forall_const]

end PEqualNP.Outside.L_meta_53195

theorem PEqualNP.Outside.L_meta_53195 : ∀ (n c : Nat) (E : Finset (Fin n × Fin n)) (color : Fin n → Fin c),
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
  ∀ (center : Fin c → Fin n) (h q : Nat) (group : Fin c → Fin (2^q)),
    (∀ j, color (center j) = j) →
    (∀ e ∈ E, e.1 = center (color e.1) ∨ e.2 = center (color e.1)) →
    (∀ j, (E.filter (fun e => group (color e.1) = j)).card < 2^h) →
    ∃ A : Finset W, keeps A ∧ A.card ≤ c+1+q+2*h ∧
      (q = 0 → 0 < h → (∃ v : Fin n, 2^(h-1) ≤
        (E.filter (fun e => e.1 = v ∨ e.2 = v)).card) →
        ∀ Z : Finset W, keeps Z → c+1+2*h ≤ Z.card) := by
  intro n c E color ordered onto connected
  dsimp only
  intro center h q group hcen hstar hgroup
  have hgroup' : ∀ j, (E.filter (fun e => group (color e.1) = j)).card < 2^h := by
    intro j
    convert hgroup j
  obtain ⟨A, hK, hcard⟩ := PEqualNP.Outside.L_meta_53195.upperBuild ordered connected center h q group hcen hstar hgroup'
  refine ⟨A, ?_, hcard, ?_⟩
  · unfold PEqualNP.Outside.L_meta_53195.Keeps PEqualNP.Outside.L_meta_53195.Can PEqualNP.Outside.L_meta_53195.seeds PEqualNP.Outside.L_meta_53195.need PEqualNP.Outside.L_meta_53195.raw PEqualNP.Outside.L_meta_53195.backward PEqualNP.Outside.L_meta_53195.forward PEqualNP.Outside.L_meta_53195.low PEqualNP.Outside.L_meta_53195.same PEqualNP.Outside.L_meta_53195.neg PEqualNP.Outside.L_meta_53195.bit at hK
    first
    | exact hK
    | (convert hK using 0 <;> congr!)
  · intro _ _ hv Z hZ
    obtain ⟨v, hv⟩ := hv
    have normalized : PEqualNP.Outside.L_meta_53195.Keeps E color Z := by
      unfold PEqualNP.Outside.L_meta_53195.Keeps PEqualNP.Outside.L_meta_53195.Can PEqualNP.Outside.L_meta_53195.seeds PEqualNP.Outside.L_meta_53195.need PEqualNP.Outside.L_meta_53195.raw PEqualNP.Outside.L_meta_53195.backward PEqualNP.Outside.L_meta_53195.forward PEqualNP.Outside.L_meta_53195.low PEqualNP.Outside.L_meta_53195.same PEqualNP.Outside.L_meta_53195.neg PEqualNP.Outside.L_meta_53195.bit
      convert hZ using 0 <;> congr!
    have := PEqualNP.Outside.L_meta_53195.starBound onto connected normalized v h (by convert hv)
    omega
