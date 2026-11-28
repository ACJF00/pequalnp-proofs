import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1511_aux

private def loadOf {n : Nat} (G : Finset (Fin n × Fin n)) (p : Fin n × Fin n → Nat) (v : Fin n) : Nat :=
  (G.filter (fun e => e.1 = v ∨ e.2 = v)).sum p

private lemma edge_ne {n : Nat} {G : Finset (Fin n × Fin n)} (hord : ∀ e ∈ G, e.1 < e.2)
    {e : Fin n × Fin n} (he : e ∈ G) : e.1 ≠ e.2 :=
  ne_of_lt (hord e he)

private lemma sum_load_eq {n : Nat} (G : Finset (Fin n × Fin n)) (p : Fin n × Fin n → Nat)
    (hord : ∀ e ∈ G, e.1 < e.2) (C : Finset (Fin n)) :
    C.sum (loadOf G p) + (G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)).sum p =
    G.sum p + (G.filter (fun e => e.1 ∈ C ∧ e.2 ∈ C)).sum p := by
  have h1 : C.sum (loadOf G p) =
      G.sum (fun e => (if e.1 ∈ C then p e else 0) + (if e.2 ∈ C then p e else 0)) := by
    unfold loadOf
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e he => ?_
    have hne : e.1 ≠ e.2 := edge_ne hord he
    have hsplit : ∀ v : Fin n, (if e.1 = v ∨ e.2 = v then p e else 0) =
        (if e.1 = v then p e else 0) + (if e.2 = v then p e else 0) := by
      intro v
      by_cases h1 : e.1 = v <;> by_cases h2 : e.2 = v
      · exact absurd (h1.trans h2.symm) hne
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_ite_eq]
  rw [h1]
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases ha : e.1 ∈ C <;> by_cases hb : e.2 ∈ C <;> simp [ha, hb] <;> omega

private lemma sum_w_identity {n : Nat} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat)
    (p : Fin n × Fin n → Nat) (hord : ∀ e ∈ G, e.1 < e.2)
    (hle : ∀ v, loadOf G p v ≤ w v) (C : Finset (Fin n)) :
    C.sum w + (G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)).sum p =
    G.sum p + C.sum (fun v => w v - loadOf G p v) +
    (G.filter (fun e => e.1 ∈ C ∧ e.2 ∈ C)).sum p := by
  have hw : C.sum w = C.sum (loadOf G p) + C.sum (fun v => w v - loadOf G p v) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    have := hle v; omega
  have hl := sum_load_eq G p hord C
  omega

private lemma exists_max_packing {n : Nat} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) :
    ∃ p : Fin n × Fin n → Nat,
      (∀ v, loadOf G p v ≤ w v) ∧
      ∀ q : Fin n × Fin n → Nat, (∀ v, loadOf G q v ≤ w v) → G.sum q ≤ G.sum p := by
  let S : Set Nat := {k | ∃ p : Fin n × Fin n → Nat, (∀ v, loadOf G p v ≤ w v) ∧ G.sum p = k}
  have hne : S.Nonempty := ⟨0, fun _ => 0, fun v => by simp [loadOf], by simp⟩
  have hbdd : BddAbove S := by
    refine ⟨Finset.univ.sum w, ?_⟩
    rintro k ⟨p, hle, rfl⟩
    calc G.sum p ≤ Finset.univ.sum (loadOf G p) := by
          unfold loadOf
          simp_rw [Finset.sum_filter]
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum fun e _ => ?_
          have hmem : e.1 ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
          calc p e = (if e.1 = e.1 ∨ e.2 = e.1 then p e else 0) := by simp
            _ ≤ ∑ x ∈ (Finset.univ : Finset (Fin n)), if e.1 = x ∨ e.2 = x then p e else 0 :=
                Finset.single_le_sum (f := fun x => if e.1 = x ∨ e.2 = x then p e else 0) (fun _ _ => Nat.zero_le _) hmem
      _ ≤ Finset.univ.sum w := Finset.sum_le_sum fun v _ => hle v
  obtain ⟨p, hle, hmax⟩ := Nat.sSup_mem hne hbdd
  refine ⟨p, hle, fun q hq => ?_⟩
  rw [hmax]
  exact le_csSup hbdd ⟨q, hq, rfl⟩

private def adjEdge {n : Nat} (G : Finset (Fin n × Fin n)) (u v : Fin n) : Option (Fin n × Fin n) :=
  if (u, v) ∈ G then some (u, v) else if (v, u) ∈ G then some (v, u) else none

private lemma adjEdge_mem {n : Nat} {G : Finset (Fin n × Fin n)} {u v : Fin n} {e : Fin n × Fin n}
    (h : adjEdge G u v = some e) :
    e ∈ G ∧ ((e = (u, v)) ∨ (e = (v, u))) := by
  unfold adjEdge at h
  split_ifs at h with h1 h2
  · cases h; exact ⟨h1, Or.inl rfl⟩
  · cases h; exact ⟨h2, Or.inr rfl⟩

private lemma adjEdge_of_mem {n : Nat} {G : Finset (Fin n × Fin n)} (hord : ∀ e ∈ G, e.1 < e.2)
    {e : Fin n × Fin n} (he : e ∈ G) :
    adjEdge G e.1 e.2 = some e ∧ adjEdge G e.2 e.1 = some e := by
  rcases e with ⟨a, b⟩
  have hlt : a < b := hord (a, b) he
  have hnot : (b, a) ∉ G := fun hba => lt_asymm hlt (hord (b, a) hba)
  constructor <;> simp [adjEdge, he, hnot]

private inductive AltReach {n : Nat} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat)
    (S : Finset (Fin n)) (p : Fin n × Fin n → Nat) : Fin n → Prop
  | start (u : Fin n) : u ∈ S → loadOf G p u < w u → AltReach G w S p u
  | fwd (u v : Fin n) (e : Fin n × Fin n) :
      AltReach G w S p u → u ∈ S → v ∉ S → adjEdge G u v = some e → AltReach G w S p v
  | bwd (v u : Fin n) (e : Fin n × Fin n) :
      AltReach G w S p v → v ∉ S → u ∈ S → adjEdge G v u = some e → 0 < p e → AltReach G w S p u

private inductive AltPath {n : Nat} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat)
    (S : Finset (Fin n)) (p : Fin n × Fin n → Nat) : List (Fin n) → Prop
  | single (u : Fin n) : u ∈ S → loadOf G p u < w u → AltPath G w S p [u]
  | fwd (u v : Fin n) (e : Fin n × Fin n) (rest : List (Fin n)) :
      AltPath G w S p (u :: rest) → u ∈ S → v ∉ S → adjEdge G u v = some e →
      AltPath G w S p (v :: u :: rest)
  | bwd (v u : Fin n) (e : Fin n × Fin n) (rest : List (Fin n)) :
      AltPath G w S p (v :: rest) → v ∉ S → u ∈ S → adjEdge G v u = some e → 0 < p e →
      AltPath G w S p (u :: v :: rest)

private lemma altReach_iff_path {n : Nat} {G : Finset (Fin n × Fin n)} {w : Fin n → Nat}
    {S : Finset (Fin n)} {p : Fin n × Fin n → Nat} {x : Fin n}
    (h : AltReach G w S p x) : ∃ L, AltPath G w S p (x :: L) := by
  induction h with
  | start u hu hlt => exact ⟨[], AltPath.single u hu hlt⟩
  | fwd u v e _ hu hv he ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨u :: L, AltPath.fwd u v e L hL hu hv he⟩
  | bwd v u e _ hv hu he hp ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨v :: L, AltPath.bwd v u e L hL hv hu he hp⟩

private lemma altPath_drop {n : Nat} {G : Finset (Fin n × Fin n)} {w : Fin n → Nat}
    {S : Finset (Fin n)} {p : Fin n × Fin n → Nat} {x : Fin n} :
    ∀ M, AltPath G w S p M → M.Nodup → x ∈ M →
      ∃ M', AltPath G w S p (x :: M') ∧ (x :: M').Nodup := by
  intro M hM hnd hxM
  induction hM with
  | single y hy hlt =>
    simp at hxM; subst hxM
    exact ⟨[], AltPath.single x hy hlt, hnd⟩
  | fwd a b e' r hr ha hb he' ihM =>
    rcases List.mem_cons.mp hxM with rfl | hmem
    · exact ⟨a :: r, AltPath.fwd a x e' r hr ha hb he', hnd⟩
    · exact ihM (List.nodup_cons.mp hnd).2 hmem
  | bwd a b e' r hr ha hb he' hp' ihM =>
    rcases List.mem_cons.mp hxM with rfl | hmem
    · exact ⟨a :: r, AltPath.bwd a x e' r hr ha hb he' hp', hnd⟩
    · exact ihM (List.nodup_cons.mp hnd).2 hmem

private lemma altPath_nodup {n : Nat} {G : Finset (Fin n × Fin n)} {w : Fin n → Nat}
    {S : Finset (Fin n)} {p : Fin n × Fin n → Nat} :
    ∀ k L, L.length ≤ k → ∀ x, AltPath G w S p (x :: L) →
      ∃ L', AltPath G w S p (x :: L') ∧ (x :: L').Nodup := by
  intro k
  induction k with
  | zero =>
    intro L hlen x hP
    have hL : L = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hL
    exact ⟨[], hP, List.nodup_singleton x⟩
  | succ k ih =>
    intro L hlen x hP
    cases hP with
    | single _ hu hlt => exact ⟨[], AltPath.single x hu hlt, List.nodup_singleton x⟩
    | fwd u _ e rest hrest hu hv he =>
      obtain ⟨L', hL', hnd⟩ := ih rest (by simp at hlen; omega) u hrest
      by_cases hx : x ∈ u :: L'
      · exact altPath_drop (u :: L') hL' hnd hx
      · exact ⟨u :: L', AltPath.fwd u x e L' hL' hu hv he, List.nodup_cons.mpr ⟨hx, hnd⟩⟩
    | bwd v _ e rest hrest hv hu he hp =>
      obtain ⟨L', hL', hnd⟩ := ih rest (by simp at hlen; omega) v hrest
      by_cases hx : x ∈ v :: L'
      · exact altPath_drop (v :: L') hL' hnd hx
      · exact ⟨v :: L', AltPath.bwd v x e L' hL' hv hu he hp, List.nodup_cons.mpr ⟨hx, hnd⟩⟩

-- Update a single edge in p by +1 or -1
private lemma loadOf_inc {n : Nat} (G : Finset (Fin n × Fin n)) (p : Fin n × Fin n → Nat)
    (hord : ∀ e ∈ G, e.1 < e.2) {e0 : Fin n × Fin n} (he0 : e0 ∈ G) (v : Fin n) :
    loadOf G (fun e => if e = e0 then p e + 1 else p e) v =
    loadOf G p v + (if e0.1 = v ∨ e0.2 = v then 1 else 0) := by
  unfold loadOf
  by_cases hv : e0.1 = v ∨ e0.2 = v
  · have hmem : e0 ∈ G.filter (fun e => e.1 = v ∨ e.2 = v) := Finset.mem_filter.mpr ⟨he0, hv⟩
    rw [if_pos hv, ← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ p hmem]
    have hrest : ∑ e ∈ (G.filter (fun e => e.1 = v ∨ e.2 = v)).erase e0,
        (if e = e0 then p e + 1 else p e) =
        ∑ e ∈ (G.filter (fun e => e.1 = v ∨ e.2 = v)).erase e0, p e := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [if_neg (Finset.ne_of_mem_erase he)]
    rw [hrest, if_pos rfl]; omega
  · rw [if_neg hv, Nat.add_zero]
    refine Finset.sum_congr rfl fun e he => ?_
    have hne : e ≠ e0 := by
      intro h; subst h; exact hv (Finset.mem_filter.mp he).2
    rw [if_neg hne]

private lemma loadOf_dec {n : Nat} (G : Finset (Fin n × Fin n)) (p : Fin n × Fin n → Nat)
    {e0 : Fin n × Fin n} (he0 : e0 ∈ G) (hp0 : 0 < p e0) (v : Fin n) :
    loadOf G (fun e => if e = e0 then p e - 1 else p e) v + (if e0.1 = v ∨ e0.2 = v then 1 else 0) =
    loadOf G p v := by
  unfold loadOf
  by_cases hv : e0.1 = v ∨ e0.2 = v
  · have hmem : e0 ∈ G.filter (fun e => e.1 = v ∨ e.2 = v) := Finset.mem_filter.mpr ⟨he0, hv⟩
    rw [if_pos hv, ← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ p hmem]
    have hrest : ∑ e ∈ (G.filter (fun e => e.1 = v ∨ e.2 = v)).erase e0,
        (if e = e0 then p e - 1 else p e) =
        ∑ e ∈ (G.filter (fun e => e.1 = v ∨ e.2 = v)).erase e0, p e := by
      refine Finset.sum_congr rfl fun e he => ?_
      rw [if_neg (Finset.ne_of_mem_erase he)]
    rw [hrest, if_pos rfl]; omega
  · rw [if_neg hv, Nat.add_zero]
    refine Finset.sum_congr rfl fun e he => ?_
    have hne : e ≠ e0 := by
      intro h; subst h; exact hv (Finset.mem_filter.mp he).2
    rw [if_neg hne]

private lemma sum_inc {n : Nat} (G : Finset (Fin n × Fin n)) (p : Fin n × Fin n → Nat)
    {e0 : Fin n × Fin n} (he0 : e0 ∈ G) :
    G.sum (fun e => if e = e0 then p e + 1 else p e) = G.sum p + 1 := by
  rw [← Finset.add_sum_erase _ _ he0, ← Finset.add_sum_erase _ p he0, if_pos rfl]
  have hrest : ∑ e ∈ G.erase e0, (if e = e0 then p e + 1 else p e) = ∑ e ∈ G.erase e0, p e :=
    Finset.sum_congr rfl fun e he => if_neg (Finset.ne_of_mem_erase he)
  rw [hrest]; omega

private lemma sum_dec {n : Nat} (G : Finset (Fin n × Fin n)) (p : Fin n × Fin n → Nat)
    {e0 : Fin n × Fin n} (he0 : e0 ∈ G) (hp0 : 0 < p e0) :
    G.sum (fun e => if e = e0 then p e - 1 else p e) + 1 = G.sum p := by
  rw [← Finset.add_sum_erase _ _ he0, ← Finset.add_sum_erase _ p he0, if_pos rfl]
  have hrest : ∑ e ∈ G.erase e0, (if e = e0 then p e - 1 else p e) = ∑ e ∈ G.erase e0, p e :=
    Finset.sum_congr rfl fun e he => if_neg (Finset.ne_of_mem_erase he)
  rw [hrest]; omega

-- Augment along a Nodup AltPath:
-- If head x ∈ S, we produce q with G.sum q = G.sum p, load q v = load p v + [v = start] - [v = x]?
-- Better: state directly for both parities!
-- Actually even cleaner:
--   For AltPath (x :: rest) with Nodup:
--   - If x ∈ S: ∃ q, G.sum q = G.sum p ∧ (∀ e, e.1 ∉ (x :: rest) → e.2 ∉ (x :: rest) → q e = p e) ∧
--       ... wait: we ONLY need q e = p e whenever e.1 ∉ rest ∧ e.2 ∉ rest? No, whenever ONE endpoint is NOT in (x :: rest)!
--   YES! Because the next edge has one endpoint = x and the other endpoint y ∉ (x :: rest),
--   so y ∉ (x :: rest) guarantees q e_next = p e_next!
private lemma augment_aux {n : Nat} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat)
    (S : Finset (Fin n)) (p : Fin n × Fin n → Nat) (hord : ∀ e ∈ G, e.1 < e.2)
    (hle : ∀ v, loadOf G p v ≤ w v) :
    ∀ L, AltPath G w S p L → L.Nodup →
      match L with
      | [] => True
      | x :: _ =>
        if x ∈ S then
          ∃ q : Fin n × Fin n → Nat,
            G.sum q = G.sum p ∧
            (∀ e, e.1 ∉ L ∨ e.2 ∉ L → q e = p e) ∧
            (∀ v, v ≠ x → loadOf G q v ≤ w v) ∧
            loadOf G q x < w x
        else
          ∃ q : Fin n × Fin n → Nat,
            G.sum q = G.sum p + 1 ∧
            (∀ e, e.1 ∉ L ∨ e.2 ∉ L → q e = p e) ∧
            (∀ v, v ≠ x → loadOf G q v ≤ w v) ∧
            loadOf G q x = loadOf G p x + 1 := by
  intro L hP hnd
  induction hP with
  | single u hu hlt =>
    simp only [hu, ↓reduceIte]
    exact ⟨p, rfl, fun _ _ => rfl, fun v _ => hle v, hlt⟩
  | fwd u v e rest hrest hu hv he ih =>
    have hnd_rest : (u :: rest).Nodup := (List.nodup_cons.mp hnd).2
    have hv_not : v ∉ u :: rest := (List.nodup_cons.mp hnd).1
    specialize ih hnd_rest
    simp only [hu, ↓reduceIte] at ih
    obtain ⟨q, hsum, hpres, hqle, hqlt⟩ := ih
    simp only [hv, ↓reduceIte]
    obtain ⟨heG, heuv⟩ := adjEdge_mem he
    have he_eq : ∀ z, (e.1 = z ∨ e.2 = z) ↔ (z = u ∨ z = v) := by
      intro z
      rcases heuv with rfl | rfl <;> exact ⟨by rintro (rfl | rfl) <;> tauto, by rintro (rfl | rfl) <;> tauto⟩
    let q' : Fin n × Fin n → Nat := fun e' => if e' = e then q e' + 1 else q e'
    refine ⟨q', ?_, ?_, ?_, ?_⟩
    · rw [sum_inc G q heG, hsum]
    · intro e' he'
      have hne : e' ≠ e := by
        intro h; subst h
        rcases he' with h1 | h2
        · apply h1; rcases heuv with rfl | rfl <;> simp
        · apply h2; rcases heuv with rfl | rfl <;> simp
      have hpres' : q e' = p e' := by
        apply hpres
        rcases he' with h1 | h2
        · exact Or.inl (fun hm => h1 (List.mem_cons_of_mem v hm))
        · exact Or.inr (fun hm => h2 (List.mem_cons_of_mem v hm))
      simp [q', hne, hpres']
    · intro z hzv
      rw [loadOf_inc G q hord heG z]
      by_cases hzu : z = u
      · subst hzu
        have hcond : e.1 = z ∨ e.2 = z := (he_eq z).mpr (Or.inl rfl)
        rw [if_pos hcond]; omega
      · have hcond : ¬ (e.1 = z ∨ e.2 = z) := by rw [he_eq]; tauto
        rw [if_neg hcond, Nat.add_zero]
        exact hqle z hzu
    · rw [loadOf_inc G q hord heG v]
      have hcond : e.1 = v ∨ e.2 = v := (he_eq v).mpr (Or.inr rfl)
      rw [if_pos hcond]
      have hqv : loadOf G q v = loadOf G p v := by
        unfold loadOf
        refine Finset.sum_congr rfl fun e' he' => ?_
        have hv_end : e'.1 = v ∨ e'.2 = v := (Finset.mem_filter.mp he').2
        apply hpres
        rcases hv_end with h1 | h2
        · exact Or.inl (by rw [h1]; exact hv_not)
        · exact Or.inr (by rw [h2]; exact hv_not)
      rw [hqv]
  | bwd v u e rest hrest hv hu he hp ih =>
    have hnd_rest : (v :: rest).Nodup := (List.nodup_cons.mp hnd).2
    have hu_not : u ∉ v :: rest := (List.nodup_cons.mp hnd).1
    specialize ih hnd_rest
    simp only [hv, ↓reduceIte] at ih
    obtain ⟨q, hsum, hpres, hqle, hqv⟩ := ih
    simp only [hu, ↓reduceIte]
    obtain ⟨heG, hevu⟩ := adjEdge_mem he
    have he_eq : ∀ z, (e.1 = z ∨ e.2 = z) ↔ (z = v ∨ z = u) := by
      intro z
      rcases hevu with rfl | rfl <;> exact ⟨by rintro (rfl | rfl) <;> tauto, by rintro (rfl | rfl) <;> tauto⟩
    have hqe : q e = p e := by
      apply hpres
      rcases hevu with rfl | rfl
      · exact Or.inr hu_not
      · exact Or.inl hu_not
    have hqepos : 0 < q e := by rw [hqe]; exact hp
    let q' : Fin n × Fin n → Nat := fun e' => if e' = e then q e' - 1 else q e'
    refine ⟨q', ?_, ?_, ?_, ?_⟩
    · have hsd := sum_dec G q heG hqepos
      change G.sum q' + 1 = G.sum q at hsd
      omega
    · intro e' he'
      have hne : e' ≠ e := by
        intro h; subst h
        rcases he' with h1 | h2
        · apply h1; rcases hevu with rfl | rfl <;> simp
        · apply h2; rcases hevu with rfl | rfl <;> simp
      have hpres' : q e' = p e' := by
        apply hpres
        rcases he' with h1 | h2
        · exact Or.inl (fun hm => h1 (List.mem_cons_of_mem u hm))
        · exact Or.inr (fun hm => h2 (List.mem_cons_of_mem u hm))
      simp [q', hne, hpres']
    · intro z hzu
      have hdec := loadOf_dec G q heG hqepos z
      change loadOf G q' z + (if e.1 = z ∨ e.2 = z then 1 else 0) = loadOf G q z at hdec
      by_cases hzv : z = v
      · subst hzv
        have hcond : e.1 = z ∨ e.2 = z := (he_eq z).mpr (Or.inl rfl)
        rw [if_pos hcond] at hdec
        have := hle z; omega
      · have hcond : ¬ (e.1 = z ∨ e.2 = z) := by rw [he_eq]; tauto
        rw [if_neg hcond, Nat.add_zero] at hdec
        rw [hdec]; exact hqle z hzv
    · have hdec := loadOf_dec G q heG hqepos u
      change loadOf G q' u + (if e.1 = u ∨ e.2 = u then 1 else 0) = loadOf G q u at hdec
      have hcond : e.1 = u ∨ e.2 = u := (he_eq u).mpr (Or.inr rfl)
      rw [if_pos hcond] at hdec
      have hqu : loadOf G q u = loadOf G p u := by
        unfold loadOf
        refine Finset.sum_congr rfl fun e' he' => ?_
        have hu_end : e'.1 = u ∨ e'.2 = u := (Finset.mem_filter.mp he').2
        apply hpres
        rcases hu_end with h1 | h2
        · exact Or.inl (by rw [h1]; exact hu_not)
        · exact Or.inr (by rw [h2]; exact hu_not)
      have := hle u; omega

private lemma no_slack_right_reach {n : Nat} (G : Finset (Fin n × Fin n)) (w : Fin n → Nat)
    (S : Finset (Fin n)) (p : Fin n × Fin n → Nat) (hord : ∀ e ∈ G, e.1 < e.2)
    (hle : ∀ v, loadOf G p v ≤ w v)
    (hmax : ∀ q : Fin n × Fin n → Nat, (∀ v, loadOf G q v ≤ w v) → G.sum q ≤ G.sum p)
    {v : Fin n} (hvS : v ∉ S) (hreach : AltReach G w S p v) :
    loadOf G p v = w v := by
  by_contra hne
  have hlt : loadOf G p v < w v := lt_of_le_of_ne (hle v) hne
  obtain ⟨L, hP⟩ := altReach_iff_path hreach
  obtain ⟨L', hP', hnd⟩ := altPath_nodup L.length L le_rfl v hP
  have haug := augment_aux G w S p hord hle (v :: L') hP' hnd
  simp only [hvS, ↓reduceIte] at haug
  obtain ⟨q, hsum, _, hqle, hqv⟩ := haug
  have hqall : ∀ z, loadOf G q z ≤ w z := by
    intro z
    by_cases hzv : z = v
    · subst hzv; omega
    · exact hqle z hzv
  have := hmax q hqall
  omega

theorem main_clean
    (n : Nat) (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (S : Finset (Fin n))
    (hbip : ∀ e ∈ G, e.1 ∉ (∅ : Finset (Fin n)) → e.2 ∉ (∅ : Finset (Fin n)) → (e.1 ∈ S ↔ e.2 ∉ S))
    (hord : ∀ e ∈ G, e.1 < e.2) :
    ∃ (p : Fin n × Fin n → Nat) (C0 : Finset (Fin n)),
      (∀ v, loadOf G p v ≤ w v) ∧
      ((∀ e ∈ G, e.1 ∈ C0 ∨ e.2 ∈ C0) ∧ ∀ B : Finset (Fin n), (∀ e ∈ G, e.1 ∈ B ∨ e.2 ∈ B) → C0.sum w ≤ B.sum w) ∧
      G.sum p = C0.sum w ∧
      ∀ C : Finset (Fin n),
        (∀ a b : Nat, b ≤ a →
          ((a + 1) * (G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)).card +
            (C.sum (fun v => w v - loadOf G p v) + (G.filter (fun e => e.1 ∈ C ∧ e.2 ∈ C)).sum p) ≤ b ↔
          (∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C) ∧ C.sum w ≤ G.sum p + b)) ∧
        C.sum w + (G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)).sum p =
        G.sum p + C.sum (fun v => w v - loadOf G p v) +
        (G.filter (fun e => e.1 ∈ C ∧ e.2 ∈ C)).sum p := by
  classical
  obtain ⟨p, hle, hmax⟩ := exists_max_packing G w
  let C0 : Finset (Fin n) := Finset.univ.filter (fun v =>
    (v ∈ S ∧ ¬ AltReach G w S p v) ∨ (v ∉ S ∧ AltReach G w S p v))
  have hcov0 : ∀ e ∈ G, e.1 ∈ C0 ∨ e.2 ∈ C0 := by
    intro e he
    have hb : e.1 ∈ S ↔ e.2 ∉ S := hbip e he (by simp) (by simp)
    obtain ⟨h12, h21⟩ := adjEdge_of_mem hord he
    by_cases h1S : e.1 ∈ S
    · have h2S : e.2 ∉ S := hb.mp h1S
      by_cases h1R : AltReach G w S p e.1
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨h2S, AltReach.fwd e.1 e.2 e h1R h1S h2S h12⟩⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨h1S, h1R⟩⟩)
    · have h2S : e.2 ∈ S := by by_contra h; exact h1S (hb.mpr h)
      by_cases h2R : AltReach G w S p e.2
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨h1S, AltReach.fwd e.2 e.1 e h2R h2S h1S h21⟩⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨h2S, h2R⟩⟩)
  have htight0 : ∀ v ∈ C0, loadOf G p v = w v := by
    intro v hv
    rcases (Finset.mem_filter.mp hv).2 with ⟨hvS, hnotR⟩ | ⟨hvS, hR⟩
    · by_contra hne
      exact hnotR (AltReach.start v hvS (lt_of_le_of_ne (hle v) hne))
    · exact no_slack_right_reach G w S p hord hle hmax hvS hR
  have hno_both0 : ∀ e ∈ G, e.1 ∈ C0 → e.2 ∈ C0 → p e = 0 := by
    intro e he h1 h2
    by_contra hp0
    have hpos : 0 < p e := Nat.pos_of_ne_zero hp0
    have hb : e.1 ∈ S ↔ e.2 ∉ S := hbip e he (by simp) (by simp)
    obtain ⟨h12, h21⟩ := adjEdge_of_mem hord he
    rcases (Finset.mem_filter.mp h1).2 with ⟨h1S, h1nR⟩ | ⟨h1nS, h1R⟩
    · have h2nS : e.2 ∉ S := hb.mp h1S
      rcases (Finset.mem_filter.mp h2).2 with ⟨h2S, _⟩ | ⟨_, h2R⟩
      · exact h2nS h2S
      · exact h1nR (AltReach.bwd e.2 e.1 e h2R h2nS h1S h21 hpos)
    · have h2S : e.2 ∈ S := by by_contra h; exact h1nS (hb.mpr h)
      rcases (Finset.mem_filter.mp h2).2 with ⟨_, h2nR⟩ | ⟨h2nS, _⟩
      · exact h2nR (AltReach.bwd e.1 e.2 e h1R h1nS h2S h12 hpos)
      · exact h2nS h2S
  have heq0 : G.sum p = C0.sum w := by
    have hid := sum_w_identity G w p hord hle C0
    have hmiss : (G.filter (fun e => e.1 ∉ C0 ∧ e.2 ∉ C0)).sum p = 0 := by
      refine Finset.sum_eq_zero fun e he => ?_
      exfalso
      rcases Finset.mem_filter.mp he with ⟨heG, h1, h2⟩
      rcases hcov0 e heG with hc1 | hc2
      · exact h1 hc1
      · exact h2 hc2
    have hslack : C0.sum (fun v => w v - loadOf G p v) = 0 := by
      refine Finset.sum_eq_zero fun v hv => ?_
      rw [htight0 v hv, Nat.sub_self]
    have hboth : (G.filter (fun e => e.1 ∈ C0 ∧ e.2 ∈ C0)).sum p = 0 := by
      refine Finset.sum_eq_zero fun e he => ?_
      rcases Finset.mem_filter.mp he with ⟨heG, h1, h2⟩
      exact hno_both0 e heG h1 h2
    omega
  refine ⟨p, C0, hle, ⟨hcov0, fun B hB => ?_⟩, heq0, fun C => ?_⟩
  · have hid := sum_w_identity G w p hord hle B
    have hmiss : (G.filter (fun e => e.1 ∉ B ∧ e.2 ∉ B)).sum p = 0 := by
      refine Finset.sum_eq_zero fun e he => ?_
      exfalso
      rcases Finset.mem_filter.mp he with ⟨heG, h1, h2⟩
      rcases hB e heG with hc1 | hc2
      · exact h1 hc1
      · exact h2 hc2
    omega
  · have hid := sum_w_identity G w p hord hle C
    refine ⟨fun a b hba => ?_, hid⟩
    constructor
    · intro hle_ab
      have hcard0 : (G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)).card = 0 := by
        by_contra hne
        have hpos : 1 ≤ (G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)).card := Nat.pos_of_ne_zero hne
        have : a + 1 ≤ (a + 1) * (G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)).card :=
          Nat.le_mul_of_pos_right (a + 1) hpos
        omega
      have hemp : G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C) = ∅ := Finset.card_eq_zero.mp hcard0
      have hcovC : ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C := by
        intro e he
        by_contra hnot
        have h1 : e.1 ∉ C := fun h => hnot (Or.inl h)
        have h2 : e.2 ∉ C := fun h => hnot (Or.inr h)
        have : e ∈ G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C) := Finset.mem_filter.mpr ⟨he, h1, h2⟩
        rw [hemp] at this; exact Finset.notMem_empty _ this
      have hmiss : (G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)).sum p = 0 := by rw [hemp]; simp
      refine ⟨hcovC, ?_⟩
      omega
    · rintro ⟨hcovC, hCw⟩
      have hemp : G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e he hnot
        rcases hcovC e he with hc1 | hc2
        · exact hnot.1 hc1
        · exact hnot.2 hc2
      have hcard0 : (G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)).card = 0 := by rw [hemp]; simp
      have hmiss : (G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)).sum p = 0 := by rw [hemp]; simp
      rw [hcard0]
      omega

end PEqualNP.Outside.L_lib_1511_aux

theorem PEqualNP.Outside.L_lib_1511 :
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    let cover := fun {N : Nat} (G : Finset (Fin N × Fin N)) (C : Finset (Fin N)) =>
      ∀ e ∈ G, e.1 ∈ C ∨ e.2 ∈ C
    let opt := fun {N : Nat} (G : Finset (Fin N × Fin N)) (w : Fin N → Nat) (C : Finset (Fin N)) =>
      cover G C ∧ ∀ B, cover G B → C.sum w ≤ B.sum w
    let bip := fun {N : Nat} (G : Finset (Fin N × Fin N)) (D S : Finset (Fin N)) =>
      ∀ e ∈ G, e.1 ∉ D → e.2 ∉ D → (e.1 ∈ S ↔ e.2 ∉ S)
    let view := fun {k N : Nat} (p : Fin k → Fin N) (C : Finset (Fin N)) =>
      Finset.univ.filter (fun i => p i ∈ C)
    ∀ (n : Nat) (G : Finset (Fin n × Fin n)) (w : Fin n → Nat) (S : Finset (Fin n)),
      bip G ∅ S → (∀ e ∈ G, e.1<e.2) →
      ∃ (p : Fin n × Fin n → Nat) (C0 : Finset (Fin n)),
        let load := fun v : Fin n => (G.filter (fun e => e.1=v ∨ e.2=v)).sum p
        (∀ v, load v ≤ w v) ∧ opt G w C0 ∧ G.sum p=C0.sum w ∧
        ∀ C : Finset (Fin n),
          let missing := G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)
          let excess := C.sum (fun v => w v-load v) + (G.filter (fun e => e.1 ∈ C ∧ e.2 ∈ C)).sum p
          (∀ a b : Nat, b ≤ a → ((a+1)*missing.card+excess ≤ b ↔ cover G C ∧ C.sum w ≤ G.sum p+b)) ∧
          C.sum w+(G.filter (fun e => e.1 ∉ C ∧ e.2 ∉ C)).sum p =
          G.sum p + C.sum (fun v => w v-load v) +
          (G.filter (fun e => e.1 ∈ C ∧ e.2 ∈ C)).sum p := by
  dsimp only
  intro n G w S hbip hord
  obtain ⟨p, C0, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_lib_1511_aux.main_clean n G w S hbip hord
  have hload : ∀ (v : Fin n) (d : DecidablePred (fun e : Fin n × Fin n => e.1 = v ∨ e.2 = v)),
      (@Finset.filter _ _ d G).sum p = PEqualNP.Outside.L_lib_1511_aux.loadOf G p v := by
    intro v d; unfold PEqualNP.Outside.L_lib_1511_aux.loadOf; congr 1; ext e; simp
  refine ⟨p, C0, ?_, h2, h3, fun C => ?_⟩
  · intro v; rw [hload v _]; exact h1 v
  · obtain ⟨ha, hb⟩ := h4 C
    have h1f : ∀ (d1 d2 : DecidablePred (fun e : Fin n × Fin n => e.1 ∉ C ∧ e.2 ∉ C)),
        @Finset.filter _ _ d1 G = @Finset.filter _ _ d2 G := fun _ _ => by ext e; simp
    have h2f : ∀ (d1 d2 : DecidablePred (fun e : Fin n × Fin n => e.1 ∈ C ∧ e.2 ∈ C)),
        @Finset.filter _ _ d1 G = @Finset.filter _ _ d2 G := fun _ _ => by ext e; simp
    have hsum : C.sum (fun v => w v - (@Finset.filter _ (fun e => e.1 = v ∨ e.2 = v) (fun e => Classical.propDecidable _) G).sum p) =
        C.sum (fun v => w v - PEqualNP.Outside.L_lib_1511_aux.loadOf G p v) :=
      Finset.sum_congr rfl fun v _ => by rw [hload v _]
    refine ⟨fun a b hba => ?_, ?_⟩
    · convert ha a b hba using 1
      rw [h1f _ _, h2f _ _, hsum]
    · convert hb using 1
      · rw [h1f _ _]
      · rw [h2f _ _, hsum]
