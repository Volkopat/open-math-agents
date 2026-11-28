import OMAStatements.S_oeis_a267474

/-!
OEIS A267474 (R. H. Hardin, Jan 15 2016): Number of length-6 0..n arrays with no following elements larger than the first repeated value.
Conjectures from Colin Barker, Feb 05 2018: G.f.: x*(38 + 152*x + 362*x^2 + 137*x^3 + 37*x^4 - 7*x^5 + x^6) / (1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Proof. The first repeated value is that of the first adjacent equal pair, and the condition only
compares entries, so it holds for an array exactly when it holds for the surjection onto Fin j
that ranks its j distinct values (`rank_decomp`): a(n) = sum_j C(n + 1, j) c_j, with c_j the
number of valid surjections Fin 6 -> Fin j. Over Fin q, the valid arrays of length m + 1 that start
with v number C(m, v) with C(0, v) = 1 and C(m + 1, v) = (v + 1)^m + sum_(a != v) C(m, a) (`G_cons`:
a repeat at the start bounds every later entry, otherwise the condition passes to the tail).
Kernel-checked tables of C give b_1..b_6, triangular elimination gives the c_j (`c_vals`), and
a(n) is an explicit polynomial of degree 6 (`a_poly`), from which the g.f. and the recurrence
follow by comparing coefficients.
-/

namespace OMA.S_oeis_a267474

open PowerSeries Finset


section engine

/-- The window condition: R holds on every three consecutive entries. -/
def Win (R : ℕ → ℕ → ℕ → Prop) {L : ℕ} (y : Fin L → ℕ) : Prop :=
  ∀ i j k : Fin L, j.val = i.val + 1 → k.val = i.val + 2 → R (y i) (y j) (y k)

instance instWin (R : ℕ → ℕ → ℕ → Prop) [∀ a b c, Decidable (R a b c)] {L : ℕ} :
    DecidablePred (Win R (L := L)) := fun y => by unfold Win; infer_instance

/-- An order embedding Fin j ↪o Fin N extended to a strictly increasing map of ℕ. -/
def ext {j N : ℕ} (e : Fin j ↪o Fin N) (k : ℕ) : ℕ := if h : k < j then (e ⟨k, h⟩ : ℕ) else N + k

lemma ext_mono {j N : ℕ} (e : Fin j ↪o Fin N) : StrictMono (ext e) := by
  intro x y hxy
  unfold ext
  split_ifs with hx hy hy
  · exact e.strictMono (show (⟨x, hx⟩ : Fin j) < ⟨y, hy⟩ from hxy)
  · have := (e ⟨x, hx⟩).isLt
    omega
  · omega
  · omega

lemma ext_apply {j N : ℕ} (e : Fin j ↪o Fin N) (r : Fin j) : ext e r = (e r : ℕ) := by
  unfold ext
  rw [dif_pos r.isLt]

/-- The arrays over Fin j that take every value and satisfy P. -/
def surjCount {L : ℕ} (P : (Fin L → ℕ) → Prop) [DecidablePred P] (j : ℕ) : ℕ :=
  ((univ : Finset (Fin L → Fin j)).filter
    (fun r : Fin L → Fin j => Function.Surjective r ∧ P (fun i => (r i : ℕ)))).card

lemma fiber_card {L : ℕ} (P : (Fin L → ℕ) → Prop) [DecidablePred P]
    (hP : ∀ f : ℕ → ℕ, StrictMono f → ∀ y : Fin L → ℕ, P (f ∘ y) ↔ P y)
    {N : ℕ} (S : Finset (Fin N)) :
    ((univ : Finset (Fin L → Fin N)).filter
      (fun x => P (fun i => (x i : ℕ)) ∧ univ.image x = S)).card = surjCount P S.card := by
  unfold surjCount
  symm
  set e := S.orderEmbOfFin rfl with he
  refine card_bij (fun r _ => fun i => e (r i)) ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    obtain ⟨hs, hp⟩ := hr
    refine ⟨?_, ?_⟩
    · have h := hP (ext e) (ext_mono e) (fun i => (r i : ℕ))
      have heq : (ext e ∘ fun i => (r i : ℕ)) = fun i => ((e (r i) : Fin N) : ℕ) := by
        funext i
        simp [ext_apply]
      rw [heq] at h
      exact h.mpr hp
    · ext y
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact S.orderEmbOfFin_mem rfl (r i)
      · intro hy
        have hy' : y ∈ Set.range e := by
          rw [he, S.range_orderEmbOfFin rfl]
          exact hy
        obtain ⟨k, rfl⟩ := hy'
        obtain ⟨i, hi⟩ := hs k
        exact ⟨i, by rw [hi]⟩
  · intro r1 _ r2 _ h
    funext i
    exact e.injective (congrFun h i)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨hp, himg⟩ := hx
    have hmem : ∀ i, x i ∈ S := fun i => by
      rw [← himg]
      exact mem_image_of_mem x (mem_univ i)
    set r : Fin L → Fin S.card := fun i => (S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩ with hr
    have hxr : ∀ i, e (r i) = x i := by
      intro i
      rw [he, ← S.coe_orderIsoOfFin_apply rfl, hr]
      simp
    refine ⟨r, ?_, funext hxr⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · intro k
      have hk : e k ∈ univ.image x := by
        rw [himg]
        exact S.orderEmbOfFin_mem rfl k
      obtain ⟨i, -, hi⟩ := mem_image.mp hk
      exact ⟨i, e.injective (by rw [hxr, hi])⟩
    · have h := hP (ext e) (ext_mono e) (fun i => (r i : ℕ))
      have heq : (ext e ∘ fun i => (r i : ℕ)) = fun i => ((x i : Fin N) : ℕ) := by
        funext i
        simp [ext_apply, hxr]
      rw [heq] at h
      exact h.mp hp

/-- Counting arrays by their value sets: an array over Fin N is the increasing enumeration of a
j-element value set composed with a surjection onto Fin j. -/
theorem rank_decomp {L : ℕ} (P : (Fin L → ℕ) → Prop) [DecidablePred P]
    (hP : ∀ f : ℕ → ℕ, StrictMono f → ∀ y : Fin L → ℕ, P (f ∘ y) ↔ P y) (N : ℕ) :
    ((univ : Finset (Fin L → Fin N)).filter (fun x => P (fun i => (x i : ℕ)))).card =
      ∑ j ∈ range (L + 1), N.choose j * surjCount P j := by
  set T : Finset (Finset (Fin N)) := univ.filter (fun S => S.card ≤ L) with hT
  rw [card_eq_sum_card_fiberwise (f := fun x => univ.image x) (t := T)]
  · have hfib : ∀ S ∈ T, (((univ : Finset (Fin L → Fin N)).filter
        (fun x => P (fun i => (x i : ℕ)))).filter (fun x => univ.image x = S)).card =
          surjCount P S.card := fun S _ => by
      rw [filter_filter]
      exact fiber_card P hP S
    have hmaps : ∀ S ∈ T, S.card ∈ range (L + 1) := by
      intro S hS
      simp only [hT, mem_filter, mem_univ, true_and] at hS
      exact mem_range.mpr (Nat.lt_succ_of_le hS)
    rw [sum_congr rfl hfib, ← sum_fiberwise_of_maps_to hmaps (fun S => surjCount P S.card)]
    refine sum_congr rfl (fun j hj => ?_)
    have hc : ∀ S ∈ T.filter (fun S => S.card = j), surjCount P S.card = surjCount P j :=
      fun S hS => by rw [(mem_filter.mp hS).2]
    rw [sum_congr rfl hc, sum_const, smul_eq_mul]
    congr 1
    have hset : T.filter (fun S => S.card = j) = powersetCard j univ := by
      ext S
      simp only [hT, mem_filter, mem_univ, true_and, mem_powersetCard_univ]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · intro h
        exact ⟨by rw [h]; exact Nat.lt_succ_iff.mp (mem_range.mp hj), h⟩
    rw [hset, card_powersetCard, card_univ, Fintype.card_fin]
  · intro x _
    simp only [hT, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    calc (univ.image x).card ≤ (univ : Finset (Fin L)).card := card_image_le
      _ = L := by simp

end engine

/-- The condition on arrays of naturals. -/
def G {L : ℕ} (y : Fin L → ℕ) : Prop :=
  ∀ i i' j : Fin L, i'.val = i.val + 1 → y i = y i' →
    (∀ k k' : Fin L, k'.val = k.val + 1 → k.val < i.val → y k ≠ y k') →
    i'.val < j.val → y j ≤ y i

instance instG {L : ℕ} : DecidablePred (G (L := L)) := fun y => by unfold G; infer_instance

lemma G_inv {L : ℕ} : ∀ f : ℕ → ℕ, StrictMono f → ∀ y : Fin L → ℕ, G (f ∘ y) ↔ G y := by
  intro f hf y
  unfold G
  simp only [Function.comp_apply, ne_eq, hf.injective.eq_iff, hf.le_iff_le]

lemma G_cons {m : ℕ} (x : ℕ) (y : Fin (m + 1) → ℕ) :
    G (Fin.cons x y : Fin (m + 2) → ℕ) ↔ if x = y 0 then ∀ j, y j ≤ x else G y := by
  unfold G
  split_ifs with hx
  · constructor
    · intro h j
      induction j using Fin.cases with
      | zero => exact le_of_eq hx.symm
      | succ j =>
        have h1 := h 0 (Fin.succ 0) (Fin.succ (Fin.succ j))
          (by simp only [Fin.val_succ, Fin.val_zero])
          (by rw [Fin.cons_zero, Fin.cons_succ]; exact hx)
          (fun k k' _ hk => absurd hk (by simp only [Fin.val_zero]; omega))
          (by simp only [Fin.val_succ, Fin.val_zero]; omega)
        simp only [Fin.cons_zero, Fin.cons_succ] at h1
        exact h1
    · intro h i i' j hi' _ hfirst hj
      have hi0 : i = 0 := by
        by_contra hne
        have hpos : 0 < i.val := Nat.pos_of_ne_zero (fun h0 => hne (Fin.ext h0))
        exact hfirst 0 (Fin.succ 0) (by simp only [Fin.val_succ, Fin.val_zero]) hpos
          (by rw [Fin.cons_zero, Fin.cons_succ]; exact hx)
      subst hi0
      induction j using Fin.cases with
      | zero => simp only [Fin.val_zero] at hj; omega
      | succ j =>
        rw [Fin.cons_zero, Fin.cons_succ]
        exact h j
  · constructor
    · intro h i i' j hi' hpair hfirst hj
      have h1 := h i.succ i'.succ j.succ (by simp only [Fin.val_succ]; omega)
        (by rw [Fin.cons_succ, Fin.cons_succ]; exact hpair)
        (fun k k' hk' hk => by
          induction k using Fin.cases with
          | zero =>
            obtain rfl : k' = Fin.succ 0 :=
              Fin.ext (by simp only [Fin.val_succ, Fin.val_zero] at hk' ⊢; omega)
            rw [Fin.cons_zero, Fin.cons_succ]
            exact hx
          | succ k =>
            induction k' using Fin.cases with
            | zero => simp only [Fin.val_succ, Fin.val_zero] at hk'; omega
            | succ k' =>
              rw [Fin.cons_succ, Fin.cons_succ]
              exact hfirst k k' (by simp only [Fin.val_succ] at hk'; omega)
                (by simp only [Fin.val_succ] at hk; omega))
        (by simp only [Fin.val_succ]; omega)
      rw [Fin.cons_succ, Fin.cons_succ] at h1
      exact h1
    · intro h i i' j hi' hpair hfirst hj
      induction i using Fin.cases with
      | zero =>
        obtain rfl : i' = Fin.succ 0 :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_zero] at hi' ⊢; omega)
        rw [Fin.cons_zero, Fin.cons_succ] at hpair
        exact absurd hpair hx
      | succ i =>
        induction i' using Fin.cases with
        | zero => simp only [Fin.val_succ, Fin.val_zero] at hi'; omega
        | succ i' =>
          induction j using Fin.cases with
          | zero => simp only [Fin.val_succ, Fin.val_zero] at hj; omega
          | succ j =>
            rw [Fin.cons_succ, Fin.cons_succ] at hpair ⊢
            refine h i i' j (by simp only [Fin.val_succ] at hi'; omega) hpair
              (fun k k' hk' hk => ?_) (by simp only [Fin.val_succ] at hj; omega)
            have h2 := hfirst k.succ k'.succ (by simp only [Fin.val_succ]; omega)
              (by simp only [Fin.val_succ]; omega)
            rwa [Fin.cons_succ, Fin.cons_succ] at h2

lemma val_cons' {m q : ℕ} (u : Fin q) (s : Fin m → Fin q) :
    (fun i => ((Fin.cons u s : Fin (m + 1) → Fin q) i : ℕ)) =
      (Fin.cons (u : ℕ) (fun i => (s i : ℕ)) : Fin (m + 1) → ℕ) := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ i => simp

/-- The valid arrays of length m + 1 over Fin q that start with v. -/
def C0 (q m : ℕ) (v : Fin q) : ℕ :=
  ((univ : Finset (Fin m → Fin q)).filter
    (fun t => G (fun i => ((Fin.cons v t : Fin (m + 1) → Fin q) i : ℕ)))).card

lemma C0_zero (q : ℕ) (v : Fin q) : C0 q 0 v = 1 := by
  unfold C0
  rw [card_eq_one]
  refine ⟨Fin.elim0, ?_⟩
  ext t
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro _
    funext i
    exact i.elim0
  · intro _ i i' j hi' _ _ _
    exact absurd i'.isLt (by omega)

lemma card_le_pow (q m : ℕ) (v : Fin q) :
    ((univ : Finset (Fin m → Fin q)).filter (fun s => ∀ j, s j ≤ v)).card = (v.val + 1) ^ m := by
  have h : (univ : Finset (Fin m → Fin q)).filter (fun s => ∀ j, s j ≤ v) =
      Fintype.piFinset (fun _ => Finset.Iic v) := by
    ext s
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  simp

lemma split_sum {q : ℕ} (v : Fin q) (P : ℕ) (Q : Fin q → ℕ) :
    ∑ b : Fin q, (if b = v then P else Q b) = P + ∑ b : Fin q, (if b = v then 0 else Q b) := by
  rw [← Finset.add_sum_erase univ _ (mem_univ v),
    ← Finset.add_sum_erase univ (fun b => if b = v then 0 else Q b) (mem_univ v)]
  simp only [if_true, zero_add]
  congr 1
  refine sum_congr rfl (fun b hb => ?_)
  rw [if_neg (ne_of_mem_erase hb), if_neg (ne_of_mem_erase hb)]

lemma C0_succ (q m : ℕ) (v : Fin q) :
    C0 q (m + 1) v = (v.val + 1) ^ m + ∑ a : Fin q, if a = v then 0 else C0 q m a := by
  rw [← split_sum]
  unfold C0
  rw [card_eq_sum_card_fiberwise (f := fun t => t 0) (t := univ) (by simp)]
  · refine sum_congr rfl (fun a _ => ?_)
    rw [filter_filter]
    by_cases ha : a = v
    · subst ha
      rw [if_pos rfl, ← card_le_pow q m a]
      refine card_bij' (fun t _ => Fin.tail t) (fun s _ => Fin.cons a s) ?_ ?_ ?_ ?_
      · intro t ht
        simp only [mem_filter, mem_univ, true_and] at ht ⊢
        obtain ⟨hG, h0⟩ := ht
        have e : t = Fin.cons a (Fin.tail t) := by
          rw [← h0]
          exact (Fin.cons_self_tail t).symm
        rw [e, val_cons', val_cons', G_cons, if_pos (by simp)] at hG
        intro j
        have := hG j.succ
        simpa using this
      · intro s hs
        simp only [mem_filter, mem_univ, true_and] at hs ⊢
        refine ⟨?_, rfl⟩
        rw [val_cons', val_cons', G_cons, if_pos (by simp)]
        intro j
        induction j using Fin.cases with
        | zero => simp
        | succ j => simpa using hs j
      · intro t ht
        simp only [mem_filter, mem_univ, true_and] at ht
        rw [← ht.2]
        exact Fin.cons_self_tail t
      · intro s _
        simp
    · rw [if_neg ha]
      refine card_bij' (fun t _ => Fin.tail t) (fun s _ => Fin.cons a s) ?_ ?_ ?_ ?_
      · intro t ht
        simp only [mem_filter, mem_univ, true_and] at ht ⊢
        obtain ⟨hG, h0⟩ := ht
        have e : t = Fin.cons a (Fin.tail t) := by
          rw [← h0]
          exact (Fin.cons_self_tail t).symm
        rw [e, val_cons', val_cons'] at hG
        rw [G_cons, if_neg (by simpa [Fin.ext_iff, eq_comm] using ha)] at hG
        rw [val_cons']
        exact hG
      · intro s hs
        simp only [mem_filter, mem_univ, true_and] at hs ⊢
        refine ⟨?_, rfl⟩
        rw [val_cons', val_cons', G_cons, if_neg (by simpa [Fin.ext_iff, eq_comm] using ha)]
        rw [val_cons'] at hs
        exact hs
      · intro t ht
        simp only [mem_filter, mem_univ, true_and] at ht
        rw [← ht.2]
        exact Fin.cons_self_tail t
      · intro s _
        simp

lemma b_eq (q m : ℕ) :
    ((univ : Finset (Fin (m + 1) → Fin q)).filter (fun x => G (fun i => (x i : ℕ)))).card =
      ∑ v : Fin q, C0 q m v := by
  rw [card_eq_sum_card_fiberwise (f := fun t => t 0) (t := univ) (by simp)]
  refine sum_congr rfl (fun v _ => ?_)
  unfold C0
  rw [filter_filter]
  refine card_bij' (fun t _ => Fin.tail t) (fun s _ => Fin.cons v s) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht ⊢
    obtain ⟨hG, h0⟩ := ht
    have e : t = Fin.cons v (Fin.tail t) := by
      rw [← h0]
      exact (Fin.cons_self_tail t).symm
    rw [e] at hG
    exact hG
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    exact ⟨hs, rfl⟩
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    rw [← ht.2]
    exact Fin.cons_self_tail t
  · intro s _
    simp

lemma C0_eq_table {q K : ℕ} (T : Fin (K + 1) → Fin q → ℕ)
    (h0 : ∀ v, T 0 v = 1)
    (hs : ∀ m : Fin K, ∀ v, T m.succ v =
      (v.val + 1) ^ m.val + ∑ a : Fin q, if a = v then 0 else T m.castSucc a) :
    ∀ m : Fin (K + 1), ∀ v, C0 q m v = T m v := by
  intro m
  induction m using Fin.induction with
  | zero =>
    intro v
    rw [Fin.val_zero, h0]
    exact C0_zero q v
  | succ m ih =>
    intro v
    rw [Fin.val_succ, C0_succ, hs]
    congr 1
    refine sum_congr rfl (fun a _ => ?_)
    rw [← ih a, Fin.val_castSucc]

lemma b_val {q K : ℕ} (T : Fin (K + 1) → Fin q → ℕ)
    (h0 : ∀ v, T 0 v = 1)
    (hs : ∀ m : Fin K, ∀ v, T m.succ v =
      (v.val + 1) ^ m.val + ∑ a : Fin q, if a = v then 0 else T m.castSucc a) :
    ((univ : Finset (Fin (K + 1) → Fin q)).filter (fun x => G (fun i => (x i : ℕ)))).card =
      ∑ v : Fin q, T (Fin.last K) v := by
  rw [b_eq]
  refine sum_congr rfl (fun v _ => ?_)
  rw [← C0_eq_table T h0 hs (Fin.last K) v, Fin.val_last]

lemma choose_q (m j : ℕ) :
    ((m.choose j : ℕ) : ℚ) = (∏ i ∈ range j, ((m : ℚ) - i)) / (j.factorial : ℚ) := by
  rw [Nat.cast_choose_eq_descPochhammer_div, descPochhammer_eval_eq_prod_range]


/-- The count over Fin q. -/
def bc (q : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin q)).filter (fun x => G (fun i => (x i : ℕ)))).card

/-- Counts over Fin 1: entry m, v is C 1 m v. -/
def T1 : Fin 6 → Fin 1 → ℕ :=
  ![![1], ![1], ![1], ![1], ![1], ![1]]

/-- Counts over Fin 2: entry m, v is C 2 m v. -/
def T2 : Fin 6 → Fin 2 → ℕ :=
  ![![1, 1], ![2, 2], ![3, 4], ![5, 7], ![8, 13], ![14, 24]]

/-- Counts over Fin 3: entry m, v is C 3 m v. -/
def T3 : Fin 6 → Fin 3 → ℕ :=
  ![![1, 1, 1], ![3, 3, 3], ![7, 8, 9], ![18, 20, 24], ![45, 50, 65], ![116, 126, 176]]

/-- Counts over Fin 4: entry m, v is C 4 m v. -/
def T4 : Fin 6 → Fin 4 → ℕ :=
  ![![1, 1, 1, 1], ![4, 4, 4, 4], ![13, 14, 15, 16], ![46, 48, 52, 58], ![159, 164, 179, 210], ![554, 564, 614, 758]]

/-- Counts over Fin 5: entry m, v is C 5 m v. -/
def T5 : Fin 6 → Fin 5 → ℕ :=
  ![![1, 1, 1, 1, 1], ![5, 5, 5, 5, 5], ![21, 22, 23, 24, 25], ![95, 97, 101, 107, 115], ![421, 426, 441, 472, 525], ![1865, 1875, 1925, 2069, 2385]]

/-- Counts over Fin 6: entry m, v is C 6 m v. -/
def T6 : Fin 6 → Fin 6 → ℕ :=
  ![![1, 1, 1, 1, 1, 1], ![6, 6, 6, 6, 6, 6], ![31, 32, 33, 34, 35, 36], ![171, 173, 177, 183, 191, 201], ![926, 931, 946, 977, 1030, 1111], ![4996, 5006, 5056, 5200, 5516, 6106]]

theorem check_all :
    ((∀ v : Fin 1, T1 0 v = 1) ∧
      (∀ m : Fin 5, ∀ v : Fin 1, T1 m.succ v =
        (v.val + 1) ^ m.val + ∑ a : Fin 1, if a = v then 0 else T1 m.castSucc a) ∧
      ∑ v : Fin 1, T1 (Fin.last 5) v = 1) ∧
    ((∀ v : Fin 2, T2 0 v = 1) ∧
      (∀ m : Fin 5, ∀ v : Fin 2, T2 m.succ v =
        (v.val + 1) ^ m.val + ∑ a : Fin 2, if a = v then 0 else T2 m.castSucc a) ∧
      ∑ v : Fin 2, T2 (Fin.last 5) v = 38) ∧
    ((∀ v : Fin 3, T3 0 v = 1) ∧
      (∀ m : Fin 5, ∀ v : Fin 3, T3 m.succ v =
        (v.val + 1) ^ m.val + ∑ a : Fin 3, if a = v then 0 else T3 m.castSucc a) ∧
      ∑ v : Fin 3, T3 (Fin.last 5) v = 418) ∧
    ((∀ v : Fin 4, T4 0 v = 1) ∧
      (∀ m : Fin 5, ∀ v : Fin 4, T4 m.succ v =
        (v.val + 1) ^ m.val + ∑ a : Fin 4, if a = v then 0 else T4 m.castSucc a) ∧
      ∑ v : Fin 4, T4 (Fin.last 5) v = 2490) ∧
    ((∀ v : Fin 5, T5 0 v = 1) ∧
      (∀ m : Fin 5, ∀ v : Fin 5, T5 m.succ v =
        (v.val + 1) ^ m.val + ∑ a : Fin 5, if a = v then 0 else T5 m.castSucc a) ∧
      ∑ v : Fin 5, T5 (Fin.last 5) v = 10119) ∧
    ((∀ v : Fin 6, T6 0 v = 1) ∧
      (∀ m : Fin 5, ∀ v : Fin 6, T6 m.succ v =
        (v.val + 1) ^ m.val + ∑ a : Fin 6, if a = v then 0 else T6 m.castSucc a) ∧
      ∑ v : Fin 6, T6 (Fin.last 5) v = 31880) := by
  decide +kernel

/-- The triangular system for the c_j, over an arbitrary function (kept apart from surjCount, whose
values the kernel would otherwise compute when it compares terms). -/
lemma solve (s : ℕ → ℕ)
    (e0 : 0 = ∑ j ∈ range 7, (0 : ℕ).choose j * s j)
    (e1 : 1 = ∑ j ∈ range 7, (1 : ℕ).choose j * s j)
    (e2 : 38 = ∑ j ∈ range 7, (2 : ℕ).choose j * s j)
    (e3 : 418 = ∑ j ∈ range 7, (3 : ℕ).choose j * s j)
    (e4 : 2490 = ∑ j ∈ range 7, (4 : ℕ).choose j * s j)
    (e5 : 10119 = ∑ j ∈ range 7, (5 : ℕ).choose j * s j)
    (e6 : 31880 = ∑ j ∈ range 7, (6 : ℕ).choose j * s j) :
    s 0 = 0 ∧ s 1 = 1 ∧ s 2 = 36 ∧ s 3 = 307 ∧ s 4 = 1042 ∧ s 5 = 1474 ∧ s 6 = 720 := by
  simp only [sum_range_succ, sum_range_zero, zero_add, one_mul, zero_mul, add_zero,
    show (0 : ℕ).choose 0 = 1 by decide, show (0 : ℕ).choose 1 = 0 by decide, show (0 : ℕ).choose 2 = 0 by decide, show (0 : ℕ).choose 3 = 0 by decide, show (0 : ℕ).choose 4 = 0 by decide, show (0 : ℕ).choose 5 = 0 by decide, show (0 : ℕ).choose 6 = 0 by decide,
    show (1 : ℕ).choose 0 = 1 by decide, show (1 : ℕ).choose 1 = 1 by decide, show (1 : ℕ).choose 2 = 0 by decide, show (1 : ℕ).choose 3 = 0 by decide, show (1 : ℕ).choose 4 = 0 by decide, show (1 : ℕ).choose 5 = 0 by decide, show (1 : ℕ).choose 6 = 0 by decide,
    show (2 : ℕ).choose 0 = 1 by decide, show (2 : ℕ).choose 1 = 2 by decide, show (2 : ℕ).choose 2 = 1 by decide, show (2 : ℕ).choose 3 = 0 by decide, show (2 : ℕ).choose 4 = 0 by decide, show (2 : ℕ).choose 5 = 0 by decide, show (2 : ℕ).choose 6 = 0 by decide,
    show (3 : ℕ).choose 0 = 1 by decide, show (3 : ℕ).choose 1 = 3 by decide, show (3 : ℕ).choose 2 = 3 by decide, show (3 : ℕ).choose 3 = 1 by decide, show (3 : ℕ).choose 4 = 0 by decide, show (3 : ℕ).choose 5 = 0 by decide, show (3 : ℕ).choose 6 = 0 by decide,
    show (4 : ℕ).choose 0 = 1 by decide, show (4 : ℕ).choose 1 = 4 by decide, show (4 : ℕ).choose 2 = 6 by decide, show (4 : ℕ).choose 3 = 4 by decide, show (4 : ℕ).choose 4 = 1 by decide, show (4 : ℕ).choose 5 = 0 by decide, show (4 : ℕ).choose 6 = 0 by decide,
    show (5 : ℕ).choose 0 = 1 by decide, show (5 : ℕ).choose 1 = 5 by decide, show (5 : ℕ).choose 2 = 10 by decide, show (5 : ℕ).choose 3 = 10 by decide, show (5 : ℕ).choose 4 = 5 by decide, show (5 : ℕ).choose 5 = 1 by decide, show (5 : ℕ).choose 6 = 0 by decide,
    show (6 : ℕ).choose 0 = 1 by decide, show (6 : ℕ).choose 1 = 6 by decide, show (6 : ℕ).choose 2 = 15 by decide, show (6 : ℕ).choose 3 = 20 by decide, show (6 : ℕ).choose 4 = 15 by decide, show (6 : ℕ).choose 5 = 6 by decide, show (6 : ℕ).choose 6 = 1 by decide] at e0 e1 e2 e3 e4 e5 e6
  omega

lemma c_vals : surjCount (G (L := 6)) 0 = 0 ∧ surjCount (G (L := 6)) 1 = 1 ∧ surjCount (G (L := 6)) 2 = 36 ∧ surjCount (G (L := 6)) 3 = 307 ∧ surjCount (G (L := 6)) 4 = 1042 ∧ surjCount (G (L := 6)) 5 = 1474 ∧ surjCount (G (L := 6)) 6 = 720 := by
  have hb1 : bc 1 = 1 := by
    have h := check_all.1
    exact (b_val T1 h.1 h.2.1).trans h.2.2
  have hb2 : bc 2 = 38 := by
    have h := check_all.2.1
    exact (b_val T2 h.1 h.2.1).trans h.2.2
  have hb3 : bc 3 = 418 := by
    have h := check_all.2.2.1
    exact (b_val T3 h.1 h.2.1).trans h.2.2
  have hb4 : bc 4 = 2490 := by
    have h := check_all.2.2.2.1
    exact (b_val T4 h.1 h.2.1).trans h.2.2
  have hb5 : bc 5 = 10119 := by
    have h := check_all.2.2.2.2.1
    exact (b_val T5 h.1 h.2.1).trans h.2.2
  have hb6 : bc 6 = 31880 := by
    have h := check_all.2.2.2.2.2
    exact (b_val T6 h.1 h.2.1).trans h.2.2
  have e0 : bc 0 = ∑ j ∈ range 7, (0 : ℕ).choose j * surjCount (G (L := 6)) j :=
    rank_decomp (G (L := 6)) G_inv 0
  have e1 : bc 1 = ∑ j ∈ range 7, (1 : ℕ).choose j * surjCount (G (L := 6)) j :=
    rank_decomp (G (L := 6)) G_inv 1
  have e2 : bc 2 = ∑ j ∈ range 7, (2 : ℕ).choose j * surjCount (G (L := 6)) j :=
    rank_decomp (G (L := 6)) G_inv 2
  have e3 : bc 3 = ∑ j ∈ range 7, (3 : ℕ).choose j * surjCount (G (L := 6)) j :=
    rank_decomp (G (L := 6)) G_inv 3
  have e4 : bc 4 = ∑ j ∈ range 7, (4 : ℕ).choose j * surjCount (G (L := 6)) j :=
    rank_decomp (G (L := 6)) G_inv 4
  have e5 : bc 5 = ∑ j ∈ range 7, (5 : ℕ).choose j * surjCount (G (L := 6)) j :=
    rank_decomp (G (L := 6)) G_inv 5
  have e6 : bc 6 = ∑ j ∈ range 7, (6 : ℕ).choose j * surjCount (G (L := 6)) j :=
    rank_decomp (G (L := 6)) G_inv 6
  have hb0 : bc 0 = 0 := (b_eq 0 5).trans (by simp)
  exact solve _ (hb0.symm.trans e0) (hb1.symm.trans e1) (hb2.symm.trans e2) (hb3.symm.trans e3) (hb4.symm.trans e4) (hb5.symm.trans e5) (hb6.symm.trans e6)

lemma a_sum (n : ℕ) : (a n : ℚ) = ∑ j ∈ range 7, (((n + 1).choose j : ℕ) : ℚ) *
    (surjCount (G (L := 6)) j : ℚ) := by
  have h := rank_decomp (G (L := 6)) G_inv (n + 1)
  have ha : a n = ((univ : Finset (Fin 6 → Fin (n + 1))).filter
      (fun x => G (fun i => (x i : ℕ)))).card := by
    unfold a
    exact congrArg Finset.card (filter_congr (fun x _ => by
      unfold good G
      simp only [ne_eq, Fin.ext_iff, Fin.le_def]))
  rw [ha, h]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- a(n) as a polynomial in n. -/
lemma a_poly (n : ℕ) : (a n : ℚ) = 1 + (149 / 30) * (n : ℚ) + 10 * (n : ℚ) ^ 2 + (43 / 4) * (n : ℚ) ^ 3 + 7 * (n : ℚ) ^ 4 + (197 / 60) * (n : ℚ) ^ 5 + (n : ℚ) ^ 6 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := c_vals
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero, choose_q, prod_range_succ, prod_range_zero,
    c0, c1, c2, c3, c4, c5, c6, Nat.factorial]
  push_cast
  ring

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (38 + 152 * X + 362 * X ^ 2 + 137 * X ^ 3 + 37 * X ^ 4 - 7 * X ^ 5 + X ^ 6) := by
  have v1 : (a 1 : ℚ) = 38 := by rw [a_poly]; norm_num
  have v2 : (a 2 : ℚ) = 418 := by rw [a_poly]; norm_num
  have v3 : (a 3 : ℚ) = 2490 := by rw [a_poly]; norm_num
  have v4 : (a 4 : ℚ) = 10119 := by rw [a_poly]; norm_num
  have v5 : (a 5 : ℚ) = 31880 := by rw [a_poly]; norm_num
  have v6 : (a 6 : ℚ) = 83972 := by rw [a_poly]; norm_num
  have v7 : (a 7 : ℚ) = 193852 := by rw [a_poly]; norm_num
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 7 = A - C (7 : ℚ) * (A * X ^ 1) + C (21 : ℚ) * (A * X ^ 2) - C (35 : ℚ) * (A * X ^ 3) + C (35 : ℚ) * (A * X ^ 4) - C (21 : ℚ) * (A * X ^ 5) + C (7 : ℚ) * (A * X ^ 6) - A * X ^ 7 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (38 + 152 * X + 362 * X ^ 2 + 137 * X ^ 3 + 37 * X ^ 4 - 7 * X ^ 5 + X ^ 6) : ℚ⟦X⟧) = X ^ 1 * C (38 : ℚ) + X ^ 2 * C (152 : ℚ) + X ^ 3 * C (362 : ℚ) + X ^ 4 * C (137 : ℚ) + X ^ 5 * C (37 : ℚ) - X ^ 6 * C (7 : ℚ) + X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk,
    coeff_C_mul]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp
  · simp [v1] <;> norm_num
  · simp [v1, v2] <;> norm_num
  · simp [v1, v2, v3] <;> norm_num
  · simp [v1, v2, v3, v4] <;> norm_num
  · simp [v1, v2, v3, v4, v5] <;> norm_num
  · simp [v1, v2, v3, v4, v5, v6] <;> norm_num
  · simp [v1, v2, v3, v4, v5, v6, v7] <;> norm_num
  · simp only [show ¬ (m + 8 = 0) by omega,
      show 1 ≤ m + 8 by omega,
      show m + 8 - 1 = m + 7 by omega,
      show ¬ (m + 7 = 0) by omega,
      show 2 ≤ m + 8 by omega,
      show m + 8 - 2 = m + 6 by omega,
      show ¬ (m + 6 = 0) by omega,
      show 3 ≤ m + 8 by omega,
      show m + 8 - 3 = m + 5 by omega,
      show ¬ (m + 5 = 0) by omega,
      show 4 ≤ m + 8 by omega,
      show m + 8 - 4 = m + 4 by omega,
      show ¬ (m + 4 = 0) by omega,
      show 5 ≤ m + 8 by omega,
      show m + 8 - 5 = m + 3 by omega,
      show ¬ (m + 3 = 0) by omega,
      show 6 ≤ m + 8 by omega,
      show m + 8 - 6 = m + 2 by omega,
      show ¬ (m + 2 = 0) by omega,
      show 7 ≤ m + 8 by omega,
      show m + 8 - 7 = m + 1 by omega,
      show ¬ (m + 1 = 0) by omega,
      show ¬ (m + 8 = 1) by omega,
      show ¬ (m + 8 = 2) by omega,
      show ¬ (m + 8 = 3) by omega,
      show ¬ (m + 8 = 4) by omega,
      show ¬ (m + 8 = 5) by omega,
      show ¬ (m + 8 = 6) by omega,
      show ¬ (m + 8 = 7) by omega, if_true, if_false]
    rw [a_poly (m + 8), a_poly (m + 7), a_poly (m + 6), a_poly (m + 5), a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1)]
    push_cast
    ring

/-- Barker's recurrence. -/
theorem recur : ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega]
  have h : (a (m + 8) : ℚ) = 7 * a (m + 7) - 21 * a (m + 6) + 35 * a (m + 5) - 35 * a (m + 4) + 21 * a (m + 3) - 7 * a (m + 2) + a (m + 1) := by
    rw [a_poly (m + 8), a_poly (m + 7), a_poly (m + 6), a_poly (m + 5), a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1)]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (38 + 152 * X + 362 * X ^ 2 + 137 * X ^ 3 + 37 * X ^ 4 - 7 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a267474

theorem OMA.solution : type_of% @OMA.S_oeis_a267474.main :=
  OMA.S_oeis_a267474.conjecture
