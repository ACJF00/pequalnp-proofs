import PEqualNP.Defs


namespace PEqualNP.Outside.L_lib_1501
open Classical
noncomputable section

def meetP {α : Type} [DecidableEq α] (P X Y : Finset α) := ((X ∩ Y) \ P) ∪ ((X ∪ Y) ∩ P)
def joinP {α : Type} [DecidableEq α] (P X Y : Finset α) := ((X ∪ Y) \ P) ∪ ((X ∩ Y) ∩ P)
def flip {α : Type} [DecidableEq α] (P X : Finset α) := (X \ P) ∪ (P \ X)

lemma flip_twice {α : Type} [DecidableEq α] (P X : Finset α) : flip P (flip P X) = X := by
  ext i
  by_cases h : i ∈ P <;> simp [flip,h]

lemma flip_meet {α : Type} [DecidableEq α] (P X Y : Finset α) :
    flip P (meetP P X Y) = flip P X ∩ flip P Y := by
  ext i
  by_cases h : i ∈ P <;> simp [flip,meetP,h]

lemma flip_join {α : Type} [DecidableEq α] (P X Y : Finset α) :
    flip P (joinP P X Y) = flip P X ∪ flip P Y := by
  ext i
  by_cases h : i ∈ P <;> simp [flip,joinP,h] <;> tauto

def Closed {α : Type} [DecidableEq α] (F : Finset (Finset α)) :=
  F.Nonempty ∧ ∀ X ∈ F, ∀ Y ∈ F, X ∩ Y ∈ F ∧ X ∪ Y ∈ F

def FixedIn {α : Type} [DecidableEq α] (F : Finset (Finset α)) (i : α) := ∀ X ∈ F, i ∈ X
def FixedOut {α : Type} [DecidableEq α] (F : Finset (Finset α)) (i : α) := ∀ X ∈ F, i ∉ X
def Forces {α : Type} [DecidableEq α] (F : Finset (Finset α)) (i j : α) := ∀ X ∈ F, i ∈ X → j ∈ X

lemma intersections {α : Type} [DecidableEq α] {F : Finset (Finset α)} (cl : Closed F)
    {H : Finset (Finset α)} (hn : H.Nonempty) (sub : H ⊆ F) :
    ∃ U ∈ F, ∀ i, i ∈ U ↔ ∀ V ∈ H, i ∈ V := by
  classical
  induction H using Finset.induction_on with
  | empty => simpa using hn
  | @insert a H na ih =>
    have af := sub (Finset.mem_insert_self a H)
    by_cases he : H.Nonempty
    · obtain ⟨B,bf,rep⟩ := ih he (fun x hx => sub (Finset.mem_insert_of_mem hx))
      refine ⟨a ∩ B,(cl.2 a af B bf).1,?_⟩
      intro i
      simp only [Finset.mem_inter,rep,Finset.forall_mem_insert]
    · have h := Finset.not_nonempty_iff_eq_empty.mp he
      subst H
      exact ⟨a,af,by simp⟩

lemma unions {α : Type} [DecidableEq α] {F : Finset (Finset α)} (cl : Closed F)
    {H : Finset (Finset α)} (hn : H.Nonempty) (sub : H ⊆ F) :
    ∃ U ∈ F, ∀ i, i ∈ U ↔ ∃ V ∈ H, i ∈ V := by
  classical
  induction H using Finset.induction_on with
  | empty => simpa using hn
  | @insert a H na ih =>
    have af := sub (Finset.mem_insert_self a H)
    by_cases he : H.Nonempty
    · obtain ⟨B,bf,rep⟩ := ih he (fun x hx => sub (Finset.mem_insert_of_mem hx))
      refine ⟨a ∪ B,(cl.2 a af B bf).2,?_⟩
      intro i
      simp only [Finset.mem_union,rep,Finset.exists_mem_insert]
    · have h := Finset.not_nonempty_iff_eq_empty.mp he
      subst H
      exact ⟨a,af,by simp⟩

lemma recoverWord {α : Type} [DecidableEq α] {F : Finset (Finset α)} (cl : Closed F) (X : Finset α)
    (one : ∀ i, FixedIn F i → i ∈ X) (zero : ∀ i, FixedOut F i → i ∉ X)
    (arrows : ∀ i j, Forces F i j → i ∈ X → j ∈ X) : X ∈ F := by
  classical
  obtain ⟨base,hbase,baseEq⟩ := intersections cl cl.1 (fun _ h => h)
  let good := F.filter (fun V => V ⊆ X)
  have bb : base ∈ good := Finset.mem_filter.mpr ⟨hbase,fun i hi => one i ((baseEq i).mp hi)⟩
  obtain ⟨W,hW,wEq⟩ := unions cl ⟨base,bb⟩ (fun _ h => (Finset.mem_filter.mp h).1)
  have eq : W = X := by
    ext i
    constructor
    · intro hi
      obtain ⟨V,hv,iv⟩ := (wEq i).mp hi
      exact (Finset.mem_filter.mp hv).2 iv
    · intro hi
      have someWord : ∃ V ∈ F, i ∈ V := by
        by_contra! h
        exact zero i h hi
      obtain ⟨V,hV,iv⟩ := someWord
      let withI := F.filter (fun Y => i ∈ Y)
      have vp : V ∈ withI := Finset.mem_filter.mpr ⟨hV,iv⟩
      obtain ⟨A,hA,eqA⟩ := intersections cl ⟨V,vp⟩ (fun _ h => (Finset.mem_filter.mp h).1)
      have subA : A ⊆ X := by
        intro j hj
        exact arrows i j (fun Y hy iy => (eqA j).mp hj Y (Finset.mem_filter.mpr ⟨hy,iy⟩)) hi
      exact (wEq i).mpr ⟨A,Finset.mem_filter.mpr ⟨hA,subA⟩,(eqA i).mpr (fun _ h => (Finset.mem_filter.mp h).2)⟩
  exact eq ▸ hW

end
end PEqualNP.Outside.L_lib_1501

namespace PEqualNP.Outside.L_lib_1501
open Classical
noncomputable section

def Cov {N : ℕ} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) : Prop :=
  ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
def Opt {N : ℕ} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) : Prop :=
  Cov G C ∧ ∀ B, Cov G B → C.card ≤ B.card
def Split {N : ℕ} (G : Finset (Fin N × Fin N)) (S : Finset (Fin N)) : Prop :=
  ∀ e ∈ G, e.1 ∈ S ↔ e.2 ∉ S
def Simple {N : ℕ} (G : Finset (Fin N × Fin N)) : Prop :=
  (∀ e ∈ G, e.1 < e.2) ∧ ∀ u : Fin N, (G.filter (fun e => u=e.1 ∨ u=e.2)).card ≤ 3
def view {k N : ℕ} (p : Fin k → Fin N) (C : Finset (Fin N)) : Finset (Fin k) :=
  Finset.univ.filter (fun i => p i ∈ C)
lemma mem_view {k N : ℕ} {p : Fin k → Fin N} {C : Finset (Fin N)} {i : Fin k} :
    i ∈ view p C ↔ p i ∈ C := by simp [view]

lemma conservation {α : Type} [DecidableEq α] (S X Y : Finset α) :
    (meetP S X Y).card + (joinP S X Y).card = X.card + Y.card := by
  have un : meetP S X Y ∪ joinP S X Y = X ∪ Y := by
    ext i
    by_cases a : i ∈ S <;> simp [meetP,joinP,a] <;> tauto
  have it : meetP S X Y ∩ joinP S X Y = X ∩ Y := by
    ext i
    by_cases a : i ∈ S <;> simp [meetP,joinP,a] <;> tauto
  have h := Finset.card_union_add_card_inter (meetP S X Y) (joinP S X Y)
  rw [un,it] at h
  exact h.symm.trans (Finset.card_union_add_card_inter X Y)

lemma mergedCovers {N : ℕ} {G : Finset (Fin N × Fin N)} {S X Y : Finset (Fin N)}
    (bip : Split G S) (cx : Cov G X) (cy : Cov G Y) :
    Cov G (meetP S X Y) ∧ Cov G (joinP S X Y) := by
  constructor <;> intro e he <;>
    have left := cx e he <;> have right := cy e he <;> have side := bip e he <;>
    simp only [meetP,joinP,Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff] <;> tauto

lemma someOptimal {N : ℕ} (G : Finset (Fin N × Fin N)) : ∃ C, Opt G C := by
  let H := (Finset.univ : Finset (Finset (Fin N))).filter (Cov G)
  have h : (Finset.univ : Finset (Fin N)) ∈ H := by simp [H,Cov]
  obtain ⟨C,hC,minimal⟩ := H.exists_min_image Finset.card ⟨_,h⟩
  exact ⟨C,(Finset.mem_filter.mp hC).2,fun B hb => minimal B (by simp [H,hb])⟩

lemma readMeet {N k : ℕ} (p : Fin k → Fin N) (S X Y : Finset (Fin N)) :
    view p (meetP S X Y) = meetP (view p S) (view p X) (view p Y) := by
  ext i
  simp only [meetP,mem_view,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
lemma readJoin {N k : ℕ} (p : Fin k → Fin N) (S X Y : Finset (Fin N)) :
    view p (joinP S X Y) = joinP (view p S) (view p X) (view p Y) := by
  ext i
  simp only [joinP,mem_view,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]

lemma necessity {k N : ℕ} {R : Finset (Finset (Fin k))} {G : Finset (Fin N × Fin N)}
    {S : Finset (Fin N)} (p : Fin k → Fin N) (sp : Split G S)
    (rep : ∀ X, X ∈ R ↔ ∃ C, Opt G C ∧ view p C = X) :
    R.Nonempty ∧ ∃ P : Finset (Fin k), ∀ X ∈ R, ∀ Y ∈ R, meetP P X Y ∈ R ∧ joinP P X Y ∈ R := by
  obtain ⟨C,hC⟩ := someOptimal G
  refine ⟨⟨view p C,(rep _).mpr ⟨C,hC,rfl⟩⟩,view p S,?_⟩
  intro X hx Y hy
  obtain ⟨A,a,rfl⟩ := (rep _).mp hx
  obtain ⟨B,b,rfl⟩ := (rep _).mp hy
  obtain ⟨m,j⟩ := mergedCovers sp a.1 b.1
  have same := conservation S A B
  have ab := a.2 B b.1
  have ba := b.2 A a.1
  have am := a.2 _ m
  have aj := a.2 _ j
  have eqm : (meetP S A B).card = A.card := by omega
  have eqj : (joinP S A B).card = A.card := by omega
  exact ⟨(rep _).mpr ⟨_,⟨m,fun V h => eqm ▸ a.2 V h⟩,readMeet p S A B⟩,
    (rep _).mpr ⟨_,⟨j,fun V h => eqj ▸ a.2 V h⟩,readJoin p S A B⟩⟩

end
end PEqualNP.Outside.L_lib_1501

namespace PEqualNP.Outside.L_lib_1501
open Classical
noncomputable section

abbrev Slot (k : ℕ) := Fin k × Fin (k+1)
abbrev Side (k : ℕ) := Slot k ⊕ Fin k
def width (k : ℕ) := Fintype.card (Side k)
abbrev Vert (k : ℕ) := Fin (width k + width k)

def label {k : ℕ} : Side k ⊕ Side k ≃ Vert k :=
  (Equiv.sumCongr (Fintype.equivFin (Side k)) (Fintype.equivFin (Side k))).trans finSumFinEquiv
def left {k : ℕ} (a : Side k) : Vert k := label (.inl a)
def right {k : ℕ} (a : Side k) : Vert k := label (.inr a)
lemma l_inj {k : ℕ} : Function.Injective (@left k) := fun _ _ h => Sum.inl.inj (label.injective h)
lemma r_inj {k : ℕ} : Function.Injective (@right k) := fun _ _ h => Sum.inr.inj (label.injective h)
lemma lr {k : ℕ} (a b : Side k) : left a ≠ right b := by
  intro h
  cases label.injective h
lemma labelCases {k : ℕ} (v : Vert k) : (∃ a, v = left a) ∨ ∃ b, v = right b := by
  obtain ⟨x,rfl⟩ := label.surjective v
  rcases x with a | b
  · exact Or.inl ⟨a,rfl⟩
  · exact Or.inr ⟨b,rfl⟩
lemma lr_lt {k : ℕ} (a b : Side k) : left a < right b := by
  change ((Fintype.equivFin (Side k) a).val : ℕ) < width k + (Fintype.equivFin (Side k) b).val
  have h : (Fintype.equivFin (Side k) a).val < width k := (Fintype.equivFin (Side k) a).isLt
  omega
lemma vertices_bound (k : ℕ) : width k + width k ≤ 4*k*k + 5*k := by
  simp [width,Side,Slot,Fintype.card_sum,Fintype.card_prod]
  nlinarith

def rot {k : ℕ} : Equiv.Perm (Side k) :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.refl _) (finRotate (k+1))) (Equiv.refl _)
lemma rotSlot {k : ℕ} (i : Fin k) (t : Fin (k+1)) :
    rot (Sum.inl (i,t)) = Sum.inl (i,finRotate (k+1) t) := rfl

def cross {k : ℕ} : Side k → Side k
  | .inl (i,t) => Fin.cases (.inr i) (fun j => .inl (j,i.succ)) t
  | .inr i => .inl (i,0)
lemma cross_twice {k : ℕ} (a : Side k) : cross (cross a) = a := by
  rcases a with ⟨i,t⟩ | i
  · refine Fin.cases ?_ (fun j => ?_) t <;> simp [cross]
  · simp [cross]

def enabled {k : ℕ} (F : Finset (Finset (Fin k))) : Side k → Prop
  | .inl (i,t) => Fin.cases (FixedIn F i) (fun j => Forces F j i) t
  | .inr i => FixedOut F i
def link {k : ℕ} (F : Finset (Finset (Fin k))) (a b : Side k) : Prop :=
  (∃ w : Slot k, a = .inl w ∧ (b = a ∨ b = rot a)) ∨ (enabled F a ∧ b = cross a)
def graph {k : ℕ} (F : Finset (Finset (Fin k))) : Finset (Vert k × Vert k) :=
  Finset.univ.filter fun e => ∃ a b : Side k, link F a b ∧ e = (left a,right b)
lemma onGraph {k : ℕ} {F : Finset (Finset (Fin k))} {e : Vert k × Vert k} :
    e ∈ graph F ↔ ∃ a b, link F a b ∧ e = (left a,right b) := by simp [graph]
lemma covGraph {k : ℕ} {F : Finset (Finset (Fin k))} {C : Finset (Vert k)} :
    Cov (graph F) C ↔ ∀ a b, link F a b → left a ∈ C ∨ right b ∈ C := by
  constructor
  · intro c a b h
    exact c (left a,right b) (onGraph.mpr ⟨a,b,h,rfl⟩)
  · intro c e he
    obtain ⟨a,b,l,rfl⟩ := onGraph.mp he
    exact c a b l

def shore (k : ℕ) : Finset (Vert k) := Finset.univ.image left
lemma graphSplit {k : ℕ} (F : Finset (Finset (Fin k))) : Split (graph F) (shore k) := by
  intro e he
  obtain ⟨a,b,_,rfl⟩ := onGraph.mp he
  have hl : left a ∈ shore k := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hr : right b ∉ shore k := by
    rintro h
    obtain ⟨c,_,eq⟩ := Finset.mem_image.mp h
    exact lr c b eq
  exact ⟨fun _ => hr,fun _ => hl⟩

lemma linkCases {k : ℕ} {F : Finset (Finset (Fin k))} {a b : Side k} (h : link F a b) :
    b = a ∨ b = rot a ∨ b = cross a := by
  rcases h with ⟨_,_,rfl | rfl⟩ | ⟨_,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

lemma boundThree {α : Type} [DecidableEq α] (s : Finset α) (a b c : α)
    (sub : ∀ e ∈ s, e = a ∨ e = b ∨ e = c) : s.card ≤ 3 := by
  have ss : s ⊆ {a,b,c} := fun e h => by simpa using sub e h
  have cap := Finset.card_le_card ss
  have h1 := Finset.card_insert_le a ({b,c} : Finset α)
  have h2 := Finset.card_insert_le b ({c} : Finset α)
  have h3 := Finset.card_singleton c
  omega

lemma graphSimple {k : ℕ} (F : Finset (Finset (Fin k))) : Simple (graph F) := by
  constructor
  · intro e he
    obtain ⟨a,b,_,rfl⟩ := onGraph.mp he
    exact lr_lt a b
  · intro v
    rcases labelCases v with ⟨x,rfl⟩ | ⟨x,rfl⟩
    · apply boundThree _ (left x,right x) (left x,right (rot x)) (left x,right (cross x))
      intro e he
      obtain ⟨mem,atx⟩ := Finset.mem_filter.mp he
      obtain ⟨a,b,ln,rfl⟩ := onGraph.mp mem
      rcases atx with h | h
      · obtain rfl := l_inj h
        rcases linkCases ln with rfl | rfl | rfl <;> simp
      · exact (lr x b h).elim
    · apply boundThree _ (left x,right x) (left (rot.symm x),right x) (left (cross x),right x)
      intro e he
      obtain ⟨mem,atx⟩ := Finset.mem_filter.mp he
      obtain ⟨a,b,ln,rfl⟩ := onGraph.mp mem
      rcases atx with h | h
      · exact (lr a x h.symm).elim
      · obtain rfl := r_inj h
        rcases linkCases ln with rfl | h | h
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (by simp [h]))
        · exact Or.inr (Or.inr (by simp [h,cross_twice]))

end
end PEqualNP.Outside.L_lib_1501

namespace PEqualNP.Outside.L_lib_1501
open Classical
noncomputable section

def select {k : ℕ} (f : Slot k → Prop) (s : Slot k) : Vert k :=
  if f s then left (.inl s) else right (.inl s)
def chosen {k : ℕ} (f : Slot k → Prop) := Finset.univ.image (select f)
lemma select_inj {k : ℕ} (f : Slot k → Prop) : Function.Injective (select f) := by
  intro a b h
  by_cases ha : f a <;> by_cases hb : f b <;> simp only [select,ha,hb,if_true,if_false] at h
  · exact Sum.inl.inj (l_inj h)
  · exact (lr _ _ h).elim
  · exact (lr _ _ h.symm).elim
  · exact Sum.inl.inj (r_inj h)
lemma chosen_card {k : ℕ} (f : Slot k → Prop) : (chosen f).card = Fintype.card (Slot k) := by
  rw [chosen,Finset.card_image_of_injective _ (select_inj f),Finset.card_univ]
lemma onLeft {k : ℕ} (f : Slot k → Prop) (a : Side k) :
    left a ∈ chosen f ↔ ∃ s, a = .inl s ∧ f s := by
  constructor
  · intro h
    obtain ⟨s,_,e⟩ := Finset.mem_image.mp h
    by_cases z : f s
    · rw [select,if_pos z] at e
      exact ⟨s,(l_inj e).symm,z⟩
    · rw [select,if_neg z] at e
      exact (lr _ _ e.symm).elim
  · rintro ⟨s,rfl,h⟩
    exact Finset.mem_image.mpr ⟨s,Finset.mem_univ _,by simp [select,h]⟩
lemma onRight {k : ℕ} (f : Slot k → Prop) (a : Side k) :
    right a ∈ chosen f ↔ ∃ s, a = .inl s ∧ ¬f s := by
  constructor
  · intro h
    obtain ⟨s,_,e⟩ := Finset.mem_image.mp h
    by_cases z : f s
    · rw [select,if_pos z] at e
      exact (lr _ _ e).elim
    · rw [select,if_neg z] at e
      exact ⟨s,(r_inj e).symm,z⟩
  · rintro ⟨s,rfl,h⟩
    exact Finset.mem_image.mpr ⟨s,Finset.mem_univ _,by simp [select,h]⟩
@[simp] lemma slotL {k : ℕ} (f : Slot k → Prop) (s : Slot k) : left (.inl s) ∈ chosen f ↔ f s := by
  simp [onLeft]
@[simp] lemma slotR {k : ℕ} (f : Slot k → Prop) (s : Slot k) : right (.inl s) ∈ chosen f ↔ ¬f s := by
  simp [onRight]
@[simp] lemma pinL {k : ℕ} (f : Slot k → Prop) (i : Fin k) : left (.inr i) ∉ chosen f := by
  simp [onLeft]
@[simp] lemma pinR {k : ℕ} (f : Slot k → Prop) (i : Fin k) : right (.inr i) ∉ chosen f := by
  simp [onRight]

def active {k : ℕ} (C : Finset (Vert k)) (s : Slot k) := left (.inl s) ∈ C
lemma matchesCovered {k : ℕ} {F : Finset (Finset (Fin k))} {C : Finset (Vert k)} (cov : Cov (graph F) C) :
    chosen (active C) ⊆ C := by
  intro v hv
  obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hv
  have edge : link F (.inl s) (.inl s) := Or.inl ⟨s,rfl,Or.inl rfl⟩
  have c := (covGraph.mp cov) _ _ edge
  by_cases h : active C s
  · rw [select,if_pos h]
    exact h
  · rw [select,if_neg h]
    exact c.resolve_left h

def pattern {k : ℕ} (X : Finset (Fin k)) := chosen (fun s : Slot k => s.1 ∈ X)

lemma wordCover {k : ℕ} {F : Finset (Finset (Fin k))} {X : Finset (Fin k)} (hX : X ∈ F) :
    Cov (graph F) (pattern X) := by
  apply covGraph.mpr
  intro a b e
  rcases e with ⟨⟨i,t⟩,rfl,rfl | rfl⟩ | ⟨en,rfl⟩
  · by_cases h : i ∈ X <;> simp [pattern,h]
  · by_cases h : i ∈ X <;> simp [pattern,rotSlot,h]
  · rcases a with ⟨i,t⟩ | i
    · induction t using Fin.cases with
      | zero =>
        have h : i ∈ X := en X hX
        simp [pattern,h]
      | succ j =>
        by_cases h : j ∈ X
        · have v : i ∈ X := en X hX h
          simp [pattern,v]
        · simp [pattern,cross,h]
    · have h : i ∉ X := en X hX
      simp [pattern,cross,h]

lemma wordOptimal {k : ℕ} {F : Finset (Finset (Fin k))} {X : Finset (Fin k)} (hX : X ∈ F) :
    Opt (graph F) (pattern X) := by
  refine ⟨wordCover hX,?_⟩
  intro C hC
  have b := Finset.card_le_card (matchesCovered hC)
  simpa only [pattern,chosen_card] using b

lemma exactlyOne {k : ℕ} {F : Finset (Finset (Fin k))} (ne : F.Nonempty)
    {C : Finset (Vert k)} (opt : Opt (graph F) C) : chosen (active C) = C := by
  obtain ⟨X,hX⟩ := ne
  apply Finset.eq_of_subset_of_card_le (matchesCovered opt.1)
  simpa only [pattern,chosen_card] using opt.2 (pattern X) (wordCover hX)

end
end PEqualNP.Outside.L_lib_1501

namespace PEqualNP.Outside.L_lib_1501
open Classical
noncomputable section

lemma cycleConstant {k : ℕ} (v : Fin (k+1) → Prop)
    (back : ∀ t, v (finRotate (k+1) t) → v t) (t : Fin (k+1)) : v t ↔ v 0 := by
  have prev (j : Fin k) : v j.succ → v j.castSucc := by
    have eq : finRotate (k+1) j.castSucc = j.succ := finRotate_of_lt j.isLt
    simpa only [eq] using back j.castSucc
  constructor
  · exact Fin.induction (fun h => h) (fun j ih h => ih (prev j h)) t
  · intro h
    have endv : v (Fin.last k) := back _ (by simpa only [finRotate_last] using h)
    exact Fin.reverseInduction endv (fun j ih => prev j ih) t

def readSlots {k : ℕ} (f : Slot k → Prop) : Finset (Fin k) :=
  Finset.univ.filter (fun i => f (i,0))
lemma bitSlots {k : ℕ} (f : Slot k → Prop) (i : Fin k) : i ∈ readSlots f ↔ f (i,0) := by simp [readSlots]

lemma wiresEqual {k : ℕ} {F : Finset (Finset (Fin k))} {f : Slot k → Prop}
    (cov : Cov (graph F) (chosen f)) (i : Fin k) (t : Fin (k+1)) : f (i,t) ↔ f (i,0) := by
  refine cycleConstant (fun u => f (i,u)) ?_ t
  intro u next
  have ed : link F (.inl (i,u)) (rot (.inl (i,u))) := Or.inl ⟨(i,u),rfl,Or.inr rfl⟩
  have holds := (covGraph.mp cov) _ _ ed
  rw [rotSlot,slotL,slotR] at holds
  exact holds.resolve_right (fun bad => bad next)

lemma constraints {k : ℕ} {F : Finset (Finset (Fin k))} (cl : Closed F) {f : Slot k → Prop}
    (cov : Cov (graph F) (chosen f)) : readSlots f ∈ F := by
  apply recoverWord cl
  · intro i hi
    apply (bitSlots _ _).mpr
    have e : link F (.inl (i,0)) (.inr i) := Or.inr ⟨hi,rfl⟩
    exact (slotL _ _).mp (((covGraph.mp cov) _ _ e).resolve_right (pinR _ _))
  · intro i hi vi
    have e : link F (.inr i) (.inl (i,0)) := Or.inr ⟨hi,rfl⟩
    have off := ((covGraph.mp cov) _ _ e).resolve_left (pinL _ _)
    exact (slotR _ _).mp off ((bitSlots _ _).mp vi)
  · intro j i arrow onj
    have e : link F (.inl (i,j.succ)) (.inl (j,i.succ)) := Or.inr ⟨arrow,rfl⟩
    have b := (covGraph.mp cov) _ _ e
    rw [slotL,slotR] at b
    have hj := (wiresEqual cov j i.succ).mpr ((bitSlots f j).mp onj)
    exact (bitSlots _ _).mpr ((wiresEqual cov i j.succ).mp (b.resolve_right (fun hn => hn hj)))

lemma allPatterns {k : ℕ} {F : Finset (Finset (Fin k))} (cl : Closed F) {C : Finset (Vert k)}
    (opt : Opt (graph F) C) : ∃ X ∈ F, C = pattern X := by
  let f := active C
  have one : chosen f = C := exactlyOne cl.1 opt
  have cov : Cov (graph F) (chosen f) := one ▸ opt.1
  refine ⟨readSlots f,constraints cl cov,?_⟩
  have shape : f = (fun s : Slot k => s.1 ∈ readSlots f) := by
    funext s
    exact propext ((wiresEqual cov s.1 s.2).trans (bitSlots f s.1).symm)
  exact one.symm.trans (congrArg chosen shape)

end
end PEqualNP.Outside.L_lib_1501

namespace PEqualNP.Outside.L_lib_1501
open Classical
noncomputable section

def port {k : ℕ} (P : Finset (Fin k)) (x : Fin k × Bool) : Vert k :=
  let s : Side k := .inl (x.1,0)
  if x.2 then (if x.1 ∈ P then right s else left s)
  else (if x.1 ∈ P then left s else right s)
lemma port_inj {k : ℕ} (P : Finset (Fin k)) : Function.Injective (port P) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  have bad {a b : Side k} : right a ≠ left b := (lr b a).symm
  cases b <;> cases c <;> by_cases hi : i ∈ P <;> by_cases hj : j ∈ P <;>
    simp_all [port,l_inj.eq_iff,r_inj.eq_iff,lr,bad]
lemma readPattern {k : ℕ} (P X : Finset (Fin k)) :
    view (fun i => port P (i,true)) (pattern X) = flip P X := by
  ext i
  by_cases hi : i ∈ P <;> simp [mem_view,pattern,port,flip,hi]
lemma partner {k : ℕ} (P X : Finset (Fin k)) (i : Fin k) :
    port P (i,false) ∈ pattern X ↔ port P (i,true) ∉ pattern X := by
  by_cases h : i ∈ P <;> simp [port,pattern,h]

def Law {k : ℕ} (R : Finset (Finset (Fin k))) :=
  R.Nonempty ∧ ∃ P : Finset (Fin k), ∀ X ∈ R, ∀ Y ∈ R, meetP P X Y ∈ R ∧ joinP P X Y ∈ R
def Realized {k : ℕ} (R : Finset (Finset (Fin k))) :=
  ∃ (N : Nat) (G : Finset (Fin N × Fin N)) (S : Finset (Fin N)) (p : Fin k × Bool → Fin N),
    N ≤ 4*k*k+5*k ∧ Simple G ∧ Split G S ∧ Function.Injective p ∧
    (∀ X, X ∈ R ↔ ∃ C, Opt G C ∧ view (fun i => p (i,true)) C = X) ∧
    (∀ C, Opt G C → ∀ i, (p (i,false) ∈ C ↔ p (i,true) ∉ C)) ∧
    ∀ C B, Opt G C → Opt G B →
      view (fun i => p (i,true)) C = view (fun i => p (i,true)) B → C=B

lemma sufficient {k : ℕ} {R : Finset (Finset (Fin k))} (h : Law R) : Realized R := by
  obtain ⟨non,P,law⟩ := h
  let F := R.image (flip P)
  have cl : Closed F := by
    constructor
    · obtain ⟨A,ha⟩ := non
      exact ⟨flip P A,Finset.mem_image_of_mem _ ha⟩
    · intro A ha B hb
      obtain ⟨X,hX,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨Y,hY,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨lm,lj⟩ := law X hX Y hY
      exact ⟨Finset.mem_image.mpr ⟨_,lm,flip_meet P X Y⟩,Finset.mem_image.mpr ⟨_,lj,flip_join P X Y⟩⟩
  refine ⟨width k + width k,graph F,shore k,port P,vertices_bound k,graphSimple _,graphSplit _,port_inj _,?_,?_,?_⟩
  · intro X
    constructor
    · intro hx
      have hF : flip P X ∈ F := Finset.mem_image_of_mem _ hx
      exact ⟨pattern (flip P X),wordOptimal hF,(readPattern P _).trans (flip_twice P X)⟩
    · rintro ⟨C,hC,rfl⟩
      obtain ⟨A,ha,rfl⟩ := allPatterns cl hC
      obtain ⟨W,hw,rfl⟩ := Finset.mem_image.mp ha
      rwa [readPattern,flip_twice]
  · intro C hC i
    obtain ⟨A,_,rfl⟩ := allPatterns cl hC
    exact partner P A i
  · intro C B hC hB eq
    obtain ⟨A,_,rfl⟩ := allPatterns cl hC
    obtain ⟨W,_,rfl⟩ := allPatterns cl hB
    rw [readPattern,readPattern] at eq
    have aw := congrArg (flip P) eq
    simp only [flip_twice] at aw
    exact congrArg pattern aw

lemma equivalence {k : ℕ} (R : Finset (Finset (Fin k))) : Law R ↔ Realized R := by
  refine ⟨sufficient,?_⟩
  rintro ⟨N,G,S,p,_,_,bip,_,words,_,_⟩
  exact necessity (fun i => p (i,true)) bip words

end
end PEqualNP.Outside.L_lib_1501


theorem PEqualNP.Outside.L_lib_1501 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let cover := fun {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
let opt := fun {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (C : Finset (Fin N)) =>
  cover G C ∧ ∀ B, cover G B → C.sum w ≤ B.sum w
let bip := fun {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) =>
  ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
let view := fun {k N : Nat} (p : Fin k → Fin N) (C : Finset (Fin N)) =>
  Finset.univ.filter (fun i => p i ∈ C)
let simple := fun {N : Nat} (G : Finset (Fin N × Fin N)) (b : Nat) =>
  (∀ e ∈ G, e.1 < e.2) ∧ ∀ u : Fin N, (G.filter (fun e => u=e.1 ∨ u=e.2)).card ≤ b
let meet := fun {k : Nat} (P X Y : Finset (Fin k)) => ((X ∩ Y) \ P) ∪ ((X ∪ Y) ∩ P)
let join := fun {k : Nat} (P X Y : Finset (Fin k)) => ((X ∪ Y) \ P) ∪ ((X ∩ Y) ∩ P)
∀ (k : Nat) (R : Finset (Finset (Fin k))),
(R.Nonempty ∧ ∃ P : Finset (Fin k), ∀ X ∈ R, ∀ Y ∈ R, meet P X Y ∈ R ∧ join P X Y ∈ R) ↔
∃ (N : Nat) (G : Finset (Fin N × Fin N)) (S : Finset (Fin N)) (p : Fin k × Bool → Fin N),
  N ≤ 4*k*k+5*k ∧ simple G 3 ∧ bip G ∅ S ∧ Function.Injective p ∧
  (∀ X, X ∈ R ↔ ∃ C, opt G (fun _ => 1) C ∧ view (fun i => p (i,true)) C=X) ∧
  (∀ C, opt G (fun _ => 1) C → ∀ i, (p (i,false) ∈ C ↔ p (i,true) ∉ C)) ∧
  ∀ C B, opt G (fun _ => 1) C → opt G (fun _ => 1) B →
    view (fun i => p (i,true)) C=view (fun i => p (i,true)) B → C=B) := by
  classical
  dsimp only
  intro k R
  have base := PEqualNP.Outside.L_lib_1501.equivalence R
  have decFin (n : ℕ) : (fun a b : Fin n => Classical.propDecidable (a=b)) = instDecidableEqFin n := Subsingleton.elim _ _
  simp [PEqualNP.Outside.L_lib_1501.Law,PEqualNP.Outside.L_lib_1501.Realized,PEqualNP.Outside.L_lib_1501.Simple,PEqualNP.Outside.L_lib_1501.Split,
    PEqualNP.Outside.L_lib_1501.Opt,PEqualNP.Outside.L_lib_1501.Cov,PEqualNP.Outside.L_lib_1501.meetP,PEqualNP.Outside.L_lib_1501.joinP,PEqualNP.Outside.L_lib_1501.view] at base ⊢
  simp only [decFin] at *
  have readSame {m n : ℕ} (t : Fin m × Bool → Fin n) (C : Finset (Fin n))
      (d : DecidablePred (fun i => t (i,true) ∈ C)) :
      @Finset.filter (Fin m) (fun i => t (i,true) ∈ C) d Finset.univ = PEqualNP.Outside.L_lib_1501.view (fun i => t (i,true)) C := by
    ext i
    simp [PEqualNP.Outside.L_lib_1501.view]
  simp only [readSame] at base ⊢
  convert! base using 0 <;> congr! 42 <;> first | rfl | (ext i; simp only [Finset.mem_filter])
