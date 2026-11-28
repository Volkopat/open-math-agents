import OMAStatements.S_oeis_a200877

/-!
OEIS A200877 (R. H. Hardin, Nov 23 2011): Number of 0..n arrays x(0..8) of 9 elements without any interior element greater than both neighbors or less than both neighbors.
Conjectures from Colin Barker, Oct 16 2017: G.f.: x*(110 + 423*x - 422*x^2 - 766*x^3 + 848*x^4 - 246*x^5 + 90*x^6 - 44*x^7 + 10*x^8 - x^9) / (1 - x)^10. a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>10.

Proof. An array over Fin N is the increasing enumeration of its j-element value set composed with
a surjection onto Fin j, and the condition only compares entries, so it holds for the array exactly
when it holds for the surjection (`rank_decomp`): a(n) = sum_j C(n + 1, j) c_j, with c_j the number
of valid surjections Fin 9 -> Fin j. The same identity with Fin q in place of Fin (n + 1) gives
b_q = sum_j C(q, j) c_j for the number b_q of valid arrays over Fin q; kernel-checked transfer
tables over the last two entries give b_1..b_9, and triangular elimination gives the c_j
(`c_vals`). So a(n) is an explicit polynomial of degree 9 (`a_poly`), and the g.f. and the
recurrence follow by comparing coefficients.
-/

namespace OMA.S_oeis_a200877

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

variable (R : ℕ → ℕ → ℕ → Prop) [∀ a b c, Decidable (R a b c)]

lemma Win_cons {m : ℕ} (x : ℕ) (y : Fin (m + 2) → ℕ) :
    Win R (Fin.cons x y : Fin (m + 3) → ℕ) ↔ R x (y 0) (y 1) ∧ Win R y := by
  unfold Win
  constructor
  · intro h
    refine ⟨?_, fun i j k hj hk => ?_⟩
    · have h0 := h 0 (0 : Fin (m + 2)).succ (1 : Fin (m + 2)).succ
        (by simp only [Fin.val_succ, Fin.val_zero]) (by simp only [Fin.val_succ, Fin.val_zero, Fin.val_one])
      rw [Fin.cons_zero, Fin.cons_succ, Fin.cons_succ] at h0
      exact h0
    · have h1 := h i.succ j.succ k.succ (by simp only [Fin.val_succ]; omega)
        (by simp only [Fin.val_succ]; omega)
      rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_succ] at h1
      exact h1
  · rintro ⟨h0, h1⟩ i j k hj hk
    induction i using Fin.cases with
    | zero =>
      obtain rfl : j = (0 : Fin (m + 2)).succ :=
        Fin.ext (by simp only [Fin.val_succ, Fin.val_zero] at hj ⊢; omega)
      obtain rfl : k = (1 : Fin (m + 2)).succ :=
        Fin.ext (by simp only [Fin.val_succ, Fin.val_zero, Fin.val_one] at hk ⊢; omega)
      rw [Fin.cons_zero, Fin.cons_succ, Fin.cons_succ]
      exact h0
    | succ i =>
      induction j using Fin.cases with
      | zero => simp only [Fin.val_succ, Fin.val_zero] at hj; omega
      | succ j =>
        induction k using Fin.cases with
        | zero => simp only [Fin.val_succ, Fin.val_zero] at hk; omega
        | succ k =>
          rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]
          exact h1 i j k (by simp only [Fin.val_succ] at hj; omega)
            (by simp only [Fin.val_succ] at hk; omega)

lemma val_cons {m q : ℕ} (u : Fin q) (s : Fin (m + 1) → Fin q) :
    (fun i => ((Fin.cons u s : Fin (m + 2) → Fin q) i : ℕ)) =
      (Fin.cons (u : ℕ) (fun i => (s i : ℕ)) : Fin (m + 2) → ℕ) := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ i => simp

/-- Arrays of length m + 2 over Fin q that start with u, v and satisfy the window condition. -/
def V (q m : ℕ) (u v : Fin q) : ℕ :=
  ((univ : Finset (Fin (m + 2) → Fin q)).filter
    (fun t => t 0 = u ∧ t 1 = v ∧ Win R (fun i => (t i : ℕ)))).card

lemma V_zero (q : ℕ) (u v : Fin q) : V R q 0 u v = 1 := by
  unfold V
  rw [card_eq_one]
  refine ⟨![u, v], ?_⟩
  ext t
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨h0, h1, -⟩
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  · rintro rfl
    refine ⟨rfl, rfl, ?_⟩
    intro i j k _ hk
    exact absurd k.isLt (by omega)

lemma V_succ (q m : ℕ) (u v : Fin q) :
    V R q (m + 1) u v = ∑ w : Fin q, if R u v w then V R q m v w else 0 := by
  unfold V
  rw [card_eq_sum_card_fiberwise (f := fun t => Fin.tail t 1) (t := univ) (by simp)]
  refine sum_congr rfl (fun w _ => ?_)
  rw [filter_filter]
  split_ifs with hw
  · refine card_bij' (fun t _ => Fin.tail t) (fun s _ => Fin.cons u s) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht ⊢
      obtain ⟨⟨h0, h1, hW⟩, h2⟩ := ht
      have e : t = Fin.cons u (Fin.tail t) := by
        rw [← h0]
        exact (Fin.cons_self_tail t).symm
      rw [e, val_cons, Win_cons] at hW
      exact ⟨h1, h2, hW.2⟩
    · intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs ⊢
      obtain ⟨h0, h1, hW⟩ := hs
      refine ⟨⟨rfl, by rw [Fin.cons_one]; exact h0, ?_⟩, by simpa using h1⟩
      rw [val_cons, Win_cons]
      refine ⟨?_, hW⟩
      rw [h0, h1]
      exact hw
    · intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht
      rw [← ht.1.1]
      exact Fin.cons_self_tail t
    · intro s _
      simp
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro t - ⟨⟨h0, h1, hW⟩, h2⟩
    have e : t = Fin.cons u (Fin.tail t) := by
      rw [← h0]
      exact (Fin.cons_self_tail t).symm
    rw [e, val_cons, Win_cons] at hW
    apply hw
    have h3 := hW.1
    rw [show Fin.tail t 0 = v from h1, h2] at h3
    exact h3

lemma b_eq (q m : ℕ) :
    ((univ : Finset (Fin (m + 2) → Fin q)).filter (fun x => Win R (fun i => (x i : ℕ)))).card =
      ∑ u : Fin q, ∑ v : Fin q, V R q m u v := by
  rw [card_eq_sum_card_fiberwise (f := fun t => (t 0, t 1)) (t := univ) (by simp)]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  refine sum_congr rfl (fun u _ => sum_congr rfl (fun v _ => ?_))
  unfold V
  rw [filter_filter]
  congr 1
  refine filter_congr (fun t _ => ?_)
  simp only [Prod.mk.injEq]
  tauto

lemma V_eq_table {q K : ℕ} (T : Fin (K + 1) → Fin q → Fin q → ℕ)
    (h0 : ∀ u v, T 0 u v = 1)
    (hs : ∀ m : Fin K, ∀ u v, T m.succ u v = ∑ w : Fin q, if R u v w then T m.castSucc v w else 0) :
    ∀ m : Fin (K + 1), ∀ u v, V R q m u v = T m u v := by
  intro m
  induction m using Fin.induction with
  | zero =>
    intro u v
    rw [Fin.val_zero, h0]
    exact V_zero R q u v
  | succ m ih =>
    intro u v
    rw [Fin.val_succ, V_succ, hs]
    refine sum_congr rfl (fun w _ => ?_)
    rw [← ih v w, Fin.coe_castSucc]

lemma b_val {q K : ℕ} (T : Fin (K + 1) → Fin q → Fin q → ℕ)
    (h0 : ∀ u v, T 0 u v = 1)
    (hs : ∀ m : Fin K, ∀ u v, T m.succ u v = ∑ w : Fin q, if R u v w then T m.castSucc v w else 0) :
    ((univ : Finset (Fin (K + 2) → Fin q)).filter (fun x => Win R (fun i => (x i : ℕ)))).card =
      ∑ u : Fin q, ∑ v : Fin q, T (Fin.last K) u v := by
  rw [b_eq]
  refine sum_congr rfl (fun u _ => sum_congr rfl (fun v _ => ?_))
  rw [← V_eq_table R T h0 hs (Fin.last K) u v, Fin.val_last]

lemma win_inv_of (hR : ∀ f : ℕ → ℕ, StrictMono f → ∀ x y z, R (f x) (f y) (f z) ↔ R x y z)
    {L : ℕ} : ∀ f : ℕ → ℕ, StrictMono f → ∀ y : Fin L → ℕ, Win R (f ∘ y) ↔ Win R y := by
  intro f hf y
  unfold Win
  simp only [Function.comp_apply, hR f hf]

end engine

lemma choose_q (m j : ℕ) :
    ((m.choose j : ℕ) : ℚ) = (∏ i ∈ range j, ((m : ℚ) - i)) / (j.factorial : ℚ) := by
  rw [Nat.cast_choose_eq_descPochhammer_div, descPochhammer_eval_eq_prod_range]

/-- The condition on three consecutive entries. -/
def Rel (x y z : ℕ) : Prop := ¬ (y > x ∧ y > z) ∧ ¬ (y < x ∧ y < z)

instance (x y z : ℕ) : Decidable (Rel x y z) := by unfold Rel; infer_instance

lemma rel_inv : ∀ f : ℕ → ℕ, StrictMono f → ∀ x y z, Rel (f x) (f y) (f z) ↔ Rel x y z := by
  intro f hf x y z
  simp only [Rel, gt_iff_lt, hf.lt_iff_lt]

lemma win_inv : ∀ f : ℕ → ℕ, StrictMono f → ∀ y : Fin 9 → ℕ, Win Rel (f ∘ y) ↔ Win Rel y :=
  win_inv_of Rel rel_inv

/-- The count over Fin q. -/
def bc (q : ℕ) : ℕ :=
  ((univ : Finset (Fin 9 → Fin q)).filter (fun x => Win Rel (fun i => (x i : ℕ)))).card

/-- Transfer table over Fin 1: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T1 : Fin 8 → Fin 1 → Fin 1 → ℕ :=
  ![![![1]], ![![1]], ![![1]], ![![1]], ![![1]], ![![1]], ![![1]], ![![1]]]

/-- Transfer table over Fin 2: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T2 : Fin 8 → Fin 2 → Fin 2 → ℕ :=
  ![![![1, 1], ![1, 1]], ![![2, 1], ![1, 2]], ![![3, 2], ![2, 3]], ![![5, 3], ![3, 5]], ![![8, 5], ![5, 8]], ![![13, 8], ![8, 13]], ![![21, 13], ![13, 21]], ![![34, 21], ![21, 34]]]

/-- Transfer table over Fin 3: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T3 : Fin 8 → Fin 3 → Fin 3 → ℕ :=
  ![![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]], ![![3, 2, 1], ![1, 3, 1], ![1, 2, 3]], ![![6, 4, 3], ![3, 5, 3], ![3, 4, 6]], ![![13, 8, 6], ![6, 11, 6], ![6, 8, 13]], ![![27, 17, 13], ![13, 23, 13], ![13, 17, 27]], ![![57, 36, 27], ![27, 49, 27], ![27, 36, 57]], ![![120, 76, 57], ![57, 103, 57], ![57, 76, 120]], ![![253, 160, 120], ![120, 217, 120], ![120, 160, 253]]]

/-- Transfer table over Fin 4: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T4 : Fin 8 → Fin 4 → Fin 4 → ℕ :=
  ![![![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1]], ![![4, 3, 2, 1], ![1, 4, 2, 1], ![1, 2, 4, 1], ![1, 2, 3, 4]], ![![10, 7, 5, 4], ![4, 8, 5, 4], ![4, 5, 8, 4], ![4, 5, 7, 10]], ![![26, 17, 12, 10], ![10, 21, 12, 10], ![10, 12, 21, 10], ![10, 12, 17, 26]], ![![65, 43, 31, 26], ![26, 53, 31, 26], ![26, 31, 53, 26], ![26, 31, 43, 65]], ![![165, 110, 79, 65], ![65, 136, 79, 65], ![65, 79, 136, 65], ![65, 79, 110, 165]], ![![419, 280, 201, 165], ![165, 345, 201, 165], ![165, 201, 345, 165], ![165, 201, 280, 419]], ![![1065, 711, 510, 419], ![419, 876, 510, 419], ![419, 510, 876, 419], ![419, 510, 711, 1065]]]

/-- Transfer table over Fin 5: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T5 : Fin 8 → Fin 5 → Fin 5 → ℕ :=
  ![![![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1]], ![![5, 4, 3, 2, 1], ![1, 5, 3, 2, 1], ![1, 2, 5, 2, 1], ![1, 2, 3, 5, 1], ![1, 2, 3, 4, 5]], ![![15, 11, 8, 6, 5], ![5, 12, 8, 6, 5], ![5, 6, 11, 6, 5], ![5, 6, 8, 12, 5], ![5, 6, 8, 11, 15]], ![![45, 31, 22, 17, 15], ![15, 36, 22, 17, 15], ![15, 17, 33, 17, 15], ![15, 17, 22, 36, 15], ![15, 17, 22, 31, 45]], ![![130, 90, 65, 51, 45], ![45, 105, 65, 51, 45], ![45, 51, 97, 51, 45], ![45, 51, 65, 105, 45], ![45, 51, 65, 90, 130]], ![![381, 266, 193, 150, 130], ![130, 311, 193, 150, 130], ![130, 150, 289, 150, 130], ![130, 150, 193, 311, 130], ![130, 150, 193, 266, 381]], ![![1120, 784, 569, 441, 381], ![381, 914, 569, 441, 381], ![381, 441, 849, 441, 381], ![381, 441, 569, 914, 381], ![381, 441, 569, 784, 1120]], ![![3295, 2305, 1671, 1295, 1120], ![1120, 2686, 1671, 1295, 1120], ![1120, 1295, 2493, 1295, 1120], ![1120, 1295, 1671, 2686, 1120], ![1120, 1295, 1671, 2305, 3295]]]

/-- Transfer table over Fin 6: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T6 : Fin 8 → Fin 6 → Fin 6 → ℕ :=
  ![![![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1]], ![![6, 5, 4, 3, 2, 1], ![1, 6, 4, 3, 2, 1], ![1, 2, 6, 3, 2, 1], ![1, 2, 3, 6, 2, 1], ![1, 2, 3, 4, 6, 1], ![1, 2, 3, 4, 5, 6]], ![![21, 16, 12, 9, 7, 6], ![6, 17, 12, 9, 7, 6], ![6, 7, 15, 9, 7, 6], ![6, 7, 9, 15, 7, 6], ![6, 7, 9, 12, 17, 6], ![6, 7, 9, 12, 16, 21]], ![![71, 51, 37, 28, 23, 21], ![21, 57, 37, 28, 23, 21], ![21, 23, 50, 28, 23, 21], ![21, 23, 28, 50, 23, 21], ![21, 23, 28, 37, 57, 21], ![21, 23, 28, 37, 51, 71]], ![![231, 166, 122, 94, 78, 71], ![71, 187, 122, 94, 78, 71], ![71, 78, 166, 94, 78, 71], ![71, 78, 94, 166, 78, 71], ![71, 78, 94, 122, 187, 71], ![71, 78, 94, 122, 166, 231]], ![![762, 552, 409, 315, 258, 231], ![231, 623, 409, 315, 258, 231], ![231, 258, 558, 315, 258, 231], ![231, 258, 315, 558, 258, 231], ![231, 258, 315, 409, 623, 231], ![231, 258, 315, 409, 552, 762]], ![![2527, 1836, 1362, 1047, 854, 762], ![762, 2067, 1362, 1047, 854, 762], ![762, 854, 1851, 1047, 854, 762], ![762, 854, 1047, 1851, 854, 762], ![762, 854, 1047, 1362, 2067, 762], ![762, 854, 1047, 1362, 1836, 2527]], ![![8388, 6092, 4514, 3467, 2829, 2527], ![2527, 6854, 4514, 3467, 2829, 2527], ![2527, 2829, 6130, 3467, 2829, 2527], ![2527, 2829, 3467, 6130, 2829, 2527], ![2527, 2829, 3467, 4514, 6854, 2527], ![2527, 2829, 3467, 4514, 6092, 8388]]]

/-- Transfer table over Fin 7: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T7 : Fin 8 → Fin 7 → Fin 7 → ℕ :=
  ![![![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1]], ![![7, 6, 5, 4, 3, 2, 1], ![1, 7, 5, 4, 3, 2, 1], ![1, 2, 7, 4, 3, 2, 1], ![1, 2, 3, 7, 3, 2, 1], ![1, 2, 3, 4, 7, 2, 1], ![1, 2, 3, 4, 5, 7, 1], ![1, 2, 3, 4, 5, 6, 7]], ![![28, 22, 17, 13, 10, 8, 7], ![7, 23, 17, 13, 10, 8, 7], ![7, 8, 20, 13, 10, 8, 7], ![7, 8, 10, 19, 10, 8, 7], ![7, 8, 10, 13, 20, 8, 7], ![7, 8, 10, 13, 17, 23, 7], ![7, 8, 10, 13, 17, 22, 28]], ![![105, 78, 58, 44, 35, 30, 28], ![28, 85, 58, 44, 35, 30, 28], ![28, 30, 73, 44, 35, 30, 28], ![28, 30, 35, 69, 35, 30, 28], ![28, 30, 35, 44, 73, 30, 28], ![28, 30, 35, 44, 58, 85, 28], ![28, 30, 35, 44, 58, 78, 105]], ![![378, 280, 210, 162, 131, 113, 105], ![105, 308, 210, 162, 131, 113, 105], ![105, 113, 268, 162, 131, 113, 105], ![105, 113, 131, 255, 131, 113, 105], ![105, 113, 131, 162, 268, 113, 105], ![105, 113, 131, 162, 210, 308, 105], ![105, 113, 131, 162, 210, 280, 378]], ![![1379, 1029, 779, 604, 486, 413, 378], ![378, 1134, 779, 604, 486, 413, 378], ![378, 413, 997, 604, 486, 413, 378], ![378, 413, 486, 953, 486, 413, 378], ![378, 413, 486, 604, 997, 413, 378], ![378, 413, 486, 604, 779, 1134, 378], ![378, 413, 486, 604, 779, 1029, 1379]], ![![5068, 3794, 2878, 2230, 1788, 1512, 1379], ![1379, 4172, 2878, 2230, 1788, 1512, 1379], ![1379, 1512, 3669, 2230, 1788, 1512, 1379], ![1379, 1512, 1788, 3507, 1788, 1512, 1379], ![1379, 1512, 1788, 2230, 3669, 1512, 1379], ![1379, 1512, 1788, 2230, 2878, 4172, 1379], ![1379, 1512, 1788, 2230, 2878, 3794, 5068]], ![![18649, 13959, 10578, 8186, 6560, 5551, 5068], ![5068, 15338, 10578, 8186, 6560, 5551, 5068], ![5068, 5551, 13469, 8186, 6560, 5551, 5068], ![5068, 5551, 6560, 12865, 6560, 5551, 5068], ![5068, 5551, 6560, 8186, 13469, 5551, 5068], ![5068, 5551, 6560, 8186, 10578, 15338, 5068], ![5068, 5551, 6560, 8186, 10578, 13959, 18649]]]

/-- Transfer table over Fin 8: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T8 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1]], ![![8, 7, 6, 5, 4, 3, 2, 1], ![1, 8, 6, 5, 4, 3, 2, 1], ![1, 2, 8, 5, 4, 3, 2, 1], ![1, 2, 3, 8, 4, 3, 2, 1], ![1, 2, 3, 4, 8, 3, 2, 1], ![1, 2, 3, 4, 5, 8, 2, 1], ![1, 2, 3, 4, 5, 6, 8, 1], ![1, 2, 3, 4, 5, 6, 7, 8]], ![![36, 29, 23, 18, 14, 11, 9, 8], ![8, 30, 23, 18, 14, 11, 9, 8], ![8, 9, 26, 18, 14, 11, 9, 8], ![8, 9, 11, 24, 14, 11, 9, 8], ![8, 9, 11, 14, 24, 11, 9, 8], ![8, 9, 11, 14, 18, 26, 9, 8], ![8, 9, 11, 14, 18, 23, 30, 8], ![8, 9, 11, 14, 18, 23, 29, 36]], ![![148, 113, 86, 66, 52, 43, 38, 36], ![36, 121, 86, 66, 52, 43, 38, 36], ![36, 38, 103, 66, 52, 43, 38, 36], ![36, 38, 43, 94, 52, 43, 38, 36], ![36, 38, 43, 52, 94, 43, 38, 36], ![36, 38, 43, 52, 66, 103, 38, 36], ![36, 38, 43, 52, 66, 86, 121, 36], ![36, 38, 43, 52, 66, 86, 113, 148]], ![![582, 442, 338, 263, 211, 177, 157, 148], ![148, 478, 338, 263, 211, 177, 157, 148], ![148, 157, 412, 263, 211, 177, 157, 148], ![148, 157, 177, 380, 211, 177, 157, 148], ![148, 157, 177, 211, 380, 177, 157, 148], ![148, 157, 177, 211, 263, 412, 157, 148], ![148, 157, 177, 211, 263, 338, 478, 148], ![148, 157, 177, 211, 263, 338, 442, 582]], ![![2318, 1772, 1368, 1073, 862, 717, 626, 582], ![582, 1920, 1368, 1073, 862, 717, 626, 582], ![582, 626, 1673, 1073, 862, 717, 626, 582], ![582, 626, 717, 1555, 862, 717, 626, 582], ![582, 626, 717, 862, 1555, 717, 626, 582], ![582, 626, 717, 862, 1073, 1673, 626, 582], ![582, 626, 717, 862, 1073, 1368, 1920, 582], ![582, 626, 717, 862, 1073, 1368, 1772, 2318]], ![![9318, 7148, 5533, 4342, 3480, 2881, 2502, 2318], ![2318, 7730, 5533, 4342, 3480, 2881, 2502, 2318], ![2318, 2502, 6741, 4342, 3480, 2881, 2502, 2318], ![2318, 2502, 2881, 6267, 3480, 2881, 2502, 2318], ![2318, 2502, 2881, 3480, 6267, 2881, 2502, 2318], ![2318, 2502, 2881, 3480, 4342, 6741, 2502, 2318], ![2318, 2502, 2881, 3480, 4342, 5533, 7730, 2318], ![2318, 2502, 2881, 3480, 4342, 5533, 7148, 9318]], ![![37522, 28786, 22264, 17448, 13968, 11561, 10048, 9318], ![9318, 31104, 22264, 17448, 13968, 11561, 10048, 9318], ![9318, 10048, 27084, 17448, 13968, 11561, 10048, 9318], ![9318, 10048, 11561, 25149, 13968, 11561, 10048, 9318], ![9318, 10048, 11561, 13968, 25149, 11561, 10048, 9318], ![9318, 10048, 11561, 13968, 17448, 27084, 10048, 9318], ![9318, 10048, 11561, 13968, 17448, 22264, 31104, 9318], ![9318, 10048, 11561, 13968, 17448, 22264, 28786, 37522]]]

/-- Transfer table over Fin 9: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T9 : Fin 8 → Fin 9 → Fin 9 → ℕ :=
  ![![![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1]], ![![9, 8, 7, 6, 5, 4, 3, 2, 1], ![1, 9, 7, 6, 5, 4, 3, 2, 1], ![1, 2, 9, 6, 5, 4, 3, 2, 1], ![1, 2, 3, 9, 5, 4, 3, 2, 1], ![1, 2, 3, 4, 9, 4, 3, 2, 1], ![1, 2, 3, 4, 5, 9, 3, 2, 1], ![1, 2, 3, 4, 5, 6, 9, 2, 1], ![1, 2, 3, 4, 5, 6, 7, 9, 1], ![1, 2, 3, 4, 5, 6, 7, 8, 9]], ![![45, 37, 30, 24, 19, 15, 12, 10, 9], ![9, 38, 30, 24, 19, 15, 12, 10, 9], ![9, 10, 33, 24, 19, 15, 12, 10, 9], ![9, 10, 12, 30, 19, 15, 12, 10, 9], ![9, 10, 12, 15, 29, 15, 12, 10, 9], ![9, 10, 12, 15, 19, 30, 12, 10, 9], ![9, 10, 12, 15, 19, 24, 33, 10, 9], ![9, 10, 12, 15, 19, 24, 30, 38, 9], ![9, 10, 12, 15, 19, 24, 30, 37, 45]], ![![201, 157, 122, 95, 75, 61, 52, 47, 45], ![45, 166, 122, 95, 75, 61, 52, 47, 45], ![45, 47, 141, 95, 75, 61, 52, 47, 45], ![45, 47, 52, 126, 75, 61, 52, 47, 45], ![45, 47, 52, 61, 121, 61, 52, 47, 45], ![45, 47, 52, 61, 75, 126, 52, 47, 45], ![45, 47, 52, 61, 75, 95, 141, 47, 45], ![45, 47, 52, 61, 75, 95, 122, 166, 45], ![45, 47, 52, 61, 75, 95, 122, 157, 201]], ![![855, 663, 516, 406, 326, 270, 233, 211, 201], ![201, 708, 516, 406, 326, 270, 233, 211, 201], ![201, 211, 608, 406, 326, 270, 233, 211, 201], ![201, 211, 233, 550, 326, 270, 233, 211, 201], ![201, 211, 233, 270, 531, 270, 233, 211, 201], ![201, 211, 233, 270, 326, 550, 233, 211, 201], ![201, 211, 233, 270, 326, 406, 608, 211, 201], ![201, 211, 233, 270, 326, 406, 516, 708, 201], ![201, 211, 233, 270, 326, 406, 516, 663, 855]], ![![3681, 2871, 2255, 1791, 1446, 1195, 1020, 909, 855], ![855, 3072, 2255, 1791, 1446, 1195, 1020, 909, 855], ![855, 909, 2667, 1791, 1446, 1195, 1020, 909, 855], ![855, 909, 1020, 2436, 1446, 1195, 1020, 909, 855], ![855, 909, 1020, 1195, 2361, 1195, 1020, 909, 855], ![855, 909, 1020, 1195, 1446, 2436, 1020, 909, 855], ![855, 909, 1020, 1195, 1446, 1791, 2667, 909, 855], ![855, 909, 1020, 1195, 1446, 1791, 2255, 3072, 855], ![855, 909, 1020, 1195, 1446, 1791, 2255, 2871, 3681]], ![![16023, 12543, 9883, 7861, 6340, 5220, 4431, 3927, 3681], ![3681, 13398, 9883, 7861, 6340, 5220, 4431, 3927, 3681], ![3681, 3927, 11647, 7861, 6340, 5220, 4431, 3927, 3681], ![3681, 3927, 4431, 10645, 6340, 5220, 4431, 3927, 3681], ![3681, 3927, 4431, 5220, 10319, 5220, 4431, 3927, 3681], ![3681, 3927, 4431, 5220, 6340, 10645, 4431, 3927, 3681], ![3681, 3927, 4431, 5220, 6340, 7861, 11647, 3927, 3681], ![3681, 3927, 4431, 5220, 6340, 7861, 9883, 13398, 3681], ![3681, 3927, 4431, 5220, 6340, 7861, 9883, 12543, 16023]], ![![69909, 54741, 43107, 34244, 27578, 22684, 19255, 17079, 16023], ![16023, 58422, 43107, 34244, 27578, 22684, 19255, 17079, 16023], ![16023, 17079, 50715, 34244, 27578, 22684, 19255, 17079, 16023], ![16023, 17079, 19255, 46283, 27578, 22684, 19255, 17079, 16023], ![16023, 17079, 19255, 22684, 44837, 22684, 19255, 17079, 16023], ![16023, 17079, 19255, 22684, 27578, 46283, 19255, 17079, 16023], ![16023, 17079, 19255, 22684, 27578, 34244, 50715, 17079, 16023], ![16023, 17079, 19255, 22684, 27578, 34244, 43107, 58422, 16023], ![16023, 17079, 19255, 22684, 27578, 34244, 43107, 54741, 69909]]]

theorem check_all :
    ((∀ u v : Fin 1, T1 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 1, T1 m.succ u v =
        ∑ w : Fin 1, if Rel u v w then T1 m.castSucc v w else 0) ∧
      ∑ u : Fin 1, ∑ v : Fin 1, T1 (Fin.last 7) u v = 1) ∧
    ((∀ u v : Fin 2, T2 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 2, T2 m.succ u v =
        ∑ w : Fin 2, if Rel u v w then T2 m.castSucc v w else 0) ∧
      ∑ u : Fin 2, ∑ v : Fin 2, T2 (Fin.last 7) u v = 110) ∧
    ((∀ u v : Fin 3, T3 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 3, T3 m.succ u v =
        ∑ w : Fin 3, if Rel u v w then T3 m.castSucc v w else 0) ∧
      ∑ u : Fin 3, ∑ v : Fin 3, T3 (Fin.last 7) u v = 1523) ∧
    ((∀ u v : Fin 4, T4 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 4, T4 m.succ u v =
        ∑ w : Fin 4, if Rel u v w then T4 m.castSucc v w else 0) ∧
      ∑ u : Fin 4, ∑ v : Fin 4, T4 (Fin.last 7) u v = 9858) ∧
    ((∀ u v : Fin 5, T5 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 5, T5 m.succ u v =
        ∑ w : Fin 5, if Rel u v w then T5 m.castSucc v w else 0) ∧
      ∑ u : Fin 5, ∑ v : Fin 5, T5 (Fin.last 7) u v = 42479) ∧
    ((∀ u v : Fin 6, T6 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 6, T6 m.succ u v =
        ∑ w : Fin 6, if Rel u v w then T6 m.castSucc v w else 0) ∧
      ∑ u : Fin 6, ∑ v : Fin 6, T6 (Fin.last 7) u v = 141688) ∧
    ((∀ u v : Fin 7, T7 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 7, T7 m.succ u v =
        ∑ w : Fin 7, if Rel u v w then T7 m.castSucc v w else 0) ∧
      ∑ u : Fin 7, ∑ v : Fin 7, T7 (Fin.last 7) u v = 395929) ∧
    ((∀ u v : Fin 8, T8 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 8, T8 m.succ u v =
        ∑ w : Fin 8, if Rel u v w then T8 m.castSucc v w else 0) ∧
      ∑ u : Fin 8, ∑ v : Fin 8, T8 (Fin.last 7) u v = 971416) ∧
    ((∀ u v : Fin 9, T9 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 9, T9 m.succ u v =
        ∑ w : Fin 9, if Rel u v w then T9 m.castSucc v w else 0) ∧
      ∑ u : Fin 9, ∑ v : Fin 9, T9 (Fin.last 7) u v = 2156867) := by
  decide +kernel

/-- The triangular system for the c_j, over an arbitrary function (kept apart from surjCount, whose
values the kernel would otherwise compute when it compares terms). -/
lemma solve (s : ℕ → ℕ)
    (e0 : 0 = ∑ j ∈ range 10, (0 : ℕ).choose j * s j)
    (e1 : 1 = ∑ j ∈ range 10, (1 : ℕ).choose j * s j)
    (e2 : 110 = ∑ j ∈ range 10, (2 : ℕ).choose j * s j)
    (e3 : 1523 = ∑ j ∈ range 10, (3 : ℕ).choose j * s j)
    (e4 : 9858 = ∑ j ∈ range 10, (4 : ℕ).choose j * s j)
    (e5 : 42479 = ∑ j ∈ range 10, (5 : ℕ).choose j * s j)
    (e6 : 141688 = ∑ j ∈ range 10, (6 : ℕ).choose j * s j)
    (e7 : 395929 = ∑ j ∈ range 10, (7 : ℕ).choose j * s j)
    (e8 : 971416 = ∑ j ∈ range 10, (8 : ℕ).choose j * s j)
    (e9 : 2156867 = ∑ j ∈ range 10, (9 : ℕ).choose j * s j) :
    s 0 = 0 ∧ s 1 = 1 ∧ s 2 = 108 ∧ s 3 = 1196 ∧ s 4 = 4422 ∧ s 5 = 7324 ∧ s 6 = 5868 ∧ s 7 = 2144 ∧ s 8 = 268 ∧ s 9 = 2 := by
  simp only [sum_range_succ, sum_range_zero, zero_add, one_mul, zero_mul, add_zero,
    show (0 : ℕ).choose 0 = 1 by decide, show (0 : ℕ).choose 1 = 0 by decide, show (0 : ℕ).choose 2 = 0 by decide, show (0 : ℕ).choose 3 = 0 by decide, show (0 : ℕ).choose 4 = 0 by decide, show (0 : ℕ).choose 5 = 0 by decide, show (0 : ℕ).choose 6 = 0 by decide, show (0 : ℕ).choose 7 = 0 by decide, show (0 : ℕ).choose 8 = 0 by decide, show (0 : ℕ).choose 9 = 0 by decide,
    show (1 : ℕ).choose 0 = 1 by decide, show (1 : ℕ).choose 1 = 1 by decide, show (1 : ℕ).choose 2 = 0 by decide, show (1 : ℕ).choose 3 = 0 by decide, show (1 : ℕ).choose 4 = 0 by decide, show (1 : ℕ).choose 5 = 0 by decide, show (1 : ℕ).choose 6 = 0 by decide, show (1 : ℕ).choose 7 = 0 by decide, show (1 : ℕ).choose 8 = 0 by decide, show (1 : ℕ).choose 9 = 0 by decide,
    show (2 : ℕ).choose 0 = 1 by decide, show (2 : ℕ).choose 1 = 2 by decide, show (2 : ℕ).choose 2 = 1 by decide, show (2 : ℕ).choose 3 = 0 by decide, show (2 : ℕ).choose 4 = 0 by decide, show (2 : ℕ).choose 5 = 0 by decide, show (2 : ℕ).choose 6 = 0 by decide, show (2 : ℕ).choose 7 = 0 by decide, show (2 : ℕ).choose 8 = 0 by decide, show (2 : ℕ).choose 9 = 0 by decide,
    show (3 : ℕ).choose 0 = 1 by decide, show (3 : ℕ).choose 1 = 3 by decide, show (3 : ℕ).choose 2 = 3 by decide, show (3 : ℕ).choose 3 = 1 by decide, show (3 : ℕ).choose 4 = 0 by decide, show (3 : ℕ).choose 5 = 0 by decide, show (3 : ℕ).choose 6 = 0 by decide, show (3 : ℕ).choose 7 = 0 by decide, show (3 : ℕ).choose 8 = 0 by decide, show (3 : ℕ).choose 9 = 0 by decide,
    show (4 : ℕ).choose 0 = 1 by decide, show (4 : ℕ).choose 1 = 4 by decide, show (4 : ℕ).choose 2 = 6 by decide, show (4 : ℕ).choose 3 = 4 by decide, show (4 : ℕ).choose 4 = 1 by decide, show (4 : ℕ).choose 5 = 0 by decide, show (4 : ℕ).choose 6 = 0 by decide, show (4 : ℕ).choose 7 = 0 by decide, show (4 : ℕ).choose 8 = 0 by decide, show (4 : ℕ).choose 9 = 0 by decide,
    show (5 : ℕ).choose 0 = 1 by decide, show (5 : ℕ).choose 1 = 5 by decide, show (5 : ℕ).choose 2 = 10 by decide, show (5 : ℕ).choose 3 = 10 by decide, show (5 : ℕ).choose 4 = 5 by decide, show (5 : ℕ).choose 5 = 1 by decide, show (5 : ℕ).choose 6 = 0 by decide, show (5 : ℕ).choose 7 = 0 by decide, show (5 : ℕ).choose 8 = 0 by decide, show (5 : ℕ).choose 9 = 0 by decide,
    show (6 : ℕ).choose 0 = 1 by decide, show (6 : ℕ).choose 1 = 6 by decide, show (6 : ℕ).choose 2 = 15 by decide, show (6 : ℕ).choose 3 = 20 by decide, show (6 : ℕ).choose 4 = 15 by decide, show (6 : ℕ).choose 5 = 6 by decide, show (6 : ℕ).choose 6 = 1 by decide, show (6 : ℕ).choose 7 = 0 by decide, show (6 : ℕ).choose 8 = 0 by decide, show (6 : ℕ).choose 9 = 0 by decide,
    show (7 : ℕ).choose 0 = 1 by decide, show (7 : ℕ).choose 1 = 7 by decide, show (7 : ℕ).choose 2 = 21 by decide, show (7 : ℕ).choose 3 = 35 by decide, show (7 : ℕ).choose 4 = 35 by decide, show (7 : ℕ).choose 5 = 21 by decide, show (7 : ℕ).choose 6 = 7 by decide, show (7 : ℕ).choose 7 = 1 by decide, show (7 : ℕ).choose 8 = 0 by decide, show (7 : ℕ).choose 9 = 0 by decide,
    show (8 : ℕ).choose 0 = 1 by decide, show (8 : ℕ).choose 1 = 8 by decide, show (8 : ℕ).choose 2 = 28 by decide, show (8 : ℕ).choose 3 = 56 by decide, show (8 : ℕ).choose 4 = 70 by decide, show (8 : ℕ).choose 5 = 56 by decide, show (8 : ℕ).choose 6 = 28 by decide, show (8 : ℕ).choose 7 = 8 by decide, show (8 : ℕ).choose 8 = 1 by decide, show (8 : ℕ).choose 9 = 0 by decide,
    show (9 : ℕ).choose 0 = 1 by decide, show (9 : ℕ).choose 1 = 9 by decide, show (9 : ℕ).choose 2 = 36 by decide, show (9 : ℕ).choose 3 = 84 by decide, show (9 : ℕ).choose 4 = 126 by decide, show (9 : ℕ).choose 5 = 126 by decide, show (9 : ℕ).choose 6 = 84 by decide, show (9 : ℕ).choose 7 = 36 by decide, show (9 : ℕ).choose 8 = 9 by decide, show (9 : ℕ).choose 9 = 1 by decide] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  omega

lemma c_vals : surjCount (Win Rel (L := 9)) 0 = 0 ∧ surjCount (Win Rel (L := 9)) 1 = 1 ∧ surjCount (Win Rel (L := 9)) 2 = 108 ∧ surjCount (Win Rel (L := 9)) 3 = 1196 ∧ surjCount (Win Rel (L := 9)) 4 = 4422 ∧ surjCount (Win Rel (L := 9)) 5 = 7324 ∧ surjCount (Win Rel (L := 9)) 6 = 5868 ∧ surjCount (Win Rel (L := 9)) 7 = 2144 ∧ surjCount (Win Rel (L := 9)) 8 = 268 ∧ surjCount (Win Rel (L := 9)) 9 = 2 := by
  have hb1 : bc 1 = 1 := by
    have h := check_all.1
    exact (b_val Rel T1 h.1 h.2.1).trans h.2.2
  have hb2 : bc 2 = 110 := by
    have h := check_all.2.1
    exact (b_val Rel T2 h.1 h.2.1).trans h.2.2
  have hb3 : bc 3 = 1523 := by
    have h := check_all.2.2.1
    exact (b_val Rel T3 h.1 h.2.1).trans h.2.2
  have hb4 : bc 4 = 9858 := by
    have h := check_all.2.2.2.1
    exact (b_val Rel T4 h.1 h.2.1).trans h.2.2
  have hb5 : bc 5 = 42479 := by
    have h := check_all.2.2.2.2.1
    exact (b_val Rel T5 h.1 h.2.1).trans h.2.2
  have hb6 : bc 6 = 141688 := by
    have h := check_all.2.2.2.2.2.1
    exact (b_val Rel T6 h.1 h.2.1).trans h.2.2
  have hb7 : bc 7 = 395929 := by
    have h := check_all.2.2.2.2.2.2.1
    exact (b_val Rel T7 h.1 h.2.1).trans h.2.2
  have hb8 : bc 8 = 971416 := by
    have h := check_all.2.2.2.2.2.2.2.1
    exact (b_val Rel T8 h.1 h.2.1).trans h.2.2
  have hb9 : bc 9 = 2156867 := by
    have h := check_all.2.2.2.2.2.2.2.2
    exact (b_val Rel T9 h.1 h.2.1).trans h.2.2
  have e0 : bc 0 = ∑ j ∈ range 10, (0 : ℕ).choose j * surjCount (Win Rel (L := 9)) j :=
    rank_decomp (Win Rel (L := 9)) win_inv 0
  have e1 : bc 1 = ∑ j ∈ range 10, (1 : ℕ).choose j * surjCount (Win Rel (L := 9)) j :=
    rank_decomp (Win Rel (L := 9)) win_inv 1
  have e2 : bc 2 = ∑ j ∈ range 10, (2 : ℕ).choose j * surjCount (Win Rel (L := 9)) j :=
    rank_decomp (Win Rel (L := 9)) win_inv 2
  have e3 : bc 3 = ∑ j ∈ range 10, (3 : ℕ).choose j * surjCount (Win Rel (L := 9)) j :=
    rank_decomp (Win Rel (L := 9)) win_inv 3
  have e4 : bc 4 = ∑ j ∈ range 10, (4 : ℕ).choose j * surjCount (Win Rel (L := 9)) j :=
    rank_decomp (Win Rel (L := 9)) win_inv 4
  have e5 : bc 5 = ∑ j ∈ range 10, (5 : ℕ).choose j * surjCount (Win Rel (L := 9)) j :=
    rank_decomp (Win Rel (L := 9)) win_inv 5
  have e6 : bc 6 = ∑ j ∈ range 10, (6 : ℕ).choose j * surjCount (Win Rel (L := 9)) j :=
    rank_decomp (Win Rel (L := 9)) win_inv 6
  have e7 : bc 7 = ∑ j ∈ range 10, (7 : ℕ).choose j * surjCount (Win Rel (L := 9)) j :=
    rank_decomp (Win Rel (L := 9)) win_inv 7
  have e8 : bc 8 = ∑ j ∈ range 10, (8 : ℕ).choose j * surjCount (Win Rel (L := 9)) j :=
    rank_decomp (Win Rel (L := 9)) win_inv 8
  have e9 : bc 9 = ∑ j ∈ range 10, (9 : ℕ).choose j * surjCount (Win Rel (L := 9)) j :=
    rank_decomp (Win Rel (L := 9)) win_inv 9
  have hb0 : bc 0 = 0 := (b_eq Rel 0 7).trans (by simp)
  exact solve _ (hb0.symm.trans e0) (hb1.symm.trans e1) (hb2.symm.trans e2) (hb3.symm.trans e3) (hb4.symm.trans e4) (hb5.symm.trans e5) (hb6.symm.trans e6) (hb7.symm.trans e7) (hb8.symm.trans e8) (hb9.symm.trans e9)

lemma a_sum (n : ℕ) : (a n : ℚ) = ∑ j ∈ range 10, (((n + 1).choose j : ℕ) : ℚ) *
    (surjCount (Win Rel (L := 9)) j : ℚ) := by
  have h := rank_decomp (Win Rel (L := 9)) win_inv (n + 1)
  have ha : a n = ((univ : Finset (Fin 9 → Fin (n + 1))).filter
      (fun x => Win Rel (fun i => (x i : ℕ)))).card := by
    unfold a
    exact congrArg Finset.card (filter_congr (fun x _ => Iff.rfl))
  rw [ha, h]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- a(n) as a polynomial in n. -/
lemma a_poly (n : ℕ) : (a n : ℚ) = 1 + (9169 / 1260) * (n : ℚ) + (36343 / 1680) * (n : ℚ) ^ 2 + (763489 / 22680) * (n : ℚ) ^ 3 + (83957 / 2880) * (n : ℚ) ^ 4 + (118933 / 8640) * (n : ℚ) ^ 5 + (4621 / 1440) * (n : ℚ) ^ 6 + (8893 / 30240) * (n : ℚ) ^ 7 + (131 / 20160) * (n : ℚ) ^ 8 + (1 / 181440) * (n : ℚ) ^ 9 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := c_vals
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero, choose_q, prod_range_succ, prod_range_zero,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, Nat.factorial]
  push_cast
  ring

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (110 + 423 * X - 422 * X ^ 2 - 766 * X ^ 3 + 848 * X ^ 4 - 246 * X ^ 5 + 90 * X ^ 6 - 44 * X ^ 7 + 10 * X ^ 8 - X ^ 9) := by
  have v1 : (a 1 : ℚ) = 110 := by rw [a_poly]; norm_num
  have v2 : (a 2 : ℚ) = 1523 := by rw [a_poly]; norm_num
  have v3 : (a 3 : ℚ) = 9858 := by rw [a_poly]; norm_num
  have v4 : (a 4 : ℚ) = 42479 := by rw [a_poly]; norm_num
  have v5 : (a 5 : ℚ) = 141688 := by rw [a_poly]; norm_num
  have v6 : (a 6 : ℚ) = 395929 := by rw [a_poly]; norm_num
  have v7 : (a 7 : ℚ) = 971416 := by rw [a_poly]; norm_num
  have v8 : (a 8 : ℚ) = 2156867 := by rw [a_poly]; norm_num
  have v9 : (a 9 : ℚ) = 4424298 := by rw [a_poly]; norm_num
  have v10 : (a 10 : ℚ) = 8509105 := by rw [a_poly]; norm_num
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 10 = A - C (10 : ℚ) * (A * X ^ 1) + C (45 : ℚ) * (A * X ^ 2) - C (120 : ℚ) * (A * X ^ 3) + C (210 : ℚ) * (A * X ^ 4) - C (252 : ℚ) * (A * X ^ 5) + C (210 : ℚ) * (A * X ^ 6) - C (120 : ℚ) * (A * X ^ 7) + C (45 : ℚ) * (A * X ^ 8) - C (10 : ℚ) * (A * X ^ 9) + A * X ^ 10 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (110 + 423 * X - 422 * X ^ 2 - 766 * X ^ 3 + 848 * X ^ 4 - 246 * X ^ 5 + 90 * X ^ 6 - 44 * X ^ 7 + 10 * X ^ 8 - X ^ 9) : ℚ⟦X⟧) = X ^ 1 * C (110 : ℚ) + X ^ 2 * C (423 : ℚ) - X ^ 3 * C (422 : ℚ) - X ^ 4 * C (766 : ℚ) + X ^ 5 * C (848 : ℚ) - X ^ 6 * C (246 : ℚ) + X ^ 7 * C (90 : ℚ) - X ^ 8 * C (44 : ℚ) + X ^ 9 * C (10 : ℚ) - X ^ 10 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk,
    coeff_C_mul]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp
  · simp [v1] <;> norm_num
  · simp [v1, v2] <;> norm_num
  · simp [v1, v2, v3] <;> norm_num
  · simp [v1, v2, v3, v4] <;> norm_num
  · simp [v1, v2, v3, v4, v5] <;> norm_num
  · simp [v1, v2, v3, v4, v5, v6] <;> norm_num
  · simp [v1, v2, v3, v4, v5, v6, v7] <;> norm_num
  · simp [v1, v2, v3, v4, v5, v6, v7, v8] <;> norm_num
  · simp [v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
  · simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
  · simp only [show ¬ (m + 11 = 0) by omega,
      show 1 ≤ m + 11 by omega,
      show ¬ (m + 11 - 1 = 0) by omega,
      show m + 11 - 1 = m + 10 by omega,
      show 2 ≤ m + 11 by omega,
      show ¬ (m + 11 - 2 = 0) by omega,
      show m + 11 - 2 = m + 9 by omega,
      show 3 ≤ m + 11 by omega,
      show ¬ (m + 11 - 3 = 0) by omega,
      show m + 11 - 3 = m + 8 by omega,
      show 4 ≤ m + 11 by omega,
      show ¬ (m + 11 - 4 = 0) by omega,
      show m + 11 - 4 = m + 7 by omega,
      show 5 ≤ m + 11 by omega,
      show ¬ (m + 11 - 5 = 0) by omega,
      show m + 11 - 5 = m + 6 by omega,
      show 6 ≤ m + 11 by omega,
      show ¬ (m + 11 - 6 = 0) by omega,
      show m + 11 - 6 = m + 5 by omega,
      show 7 ≤ m + 11 by omega,
      show ¬ (m + 11 - 7 = 0) by omega,
      show m + 11 - 7 = m + 4 by omega,
      show 8 ≤ m + 11 by omega,
      show ¬ (m + 11 - 8 = 0) by omega,
      show m + 11 - 8 = m + 3 by omega,
      show 9 ≤ m + 11 by omega,
      show ¬ (m + 11 - 9 = 0) by omega,
      show m + 11 - 9 = m + 2 by omega,
      show 10 ≤ m + 11 by omega,
      show ¬ (m + 11 - 10 = 0) by omega,
      show m + 11 - 10 = m + 1 by omega,
      show ¬ (m + 11 = 1) by omega,
      show ¬ (m + 11 = 2) by omega,
      show ¬ (m + 11 = 3) by omega,
      show ¬ (m + 11 = 4) by omega,
      show ¬ (m + 11 = 5) by omega,
      show ¬ (m + 11 = 6) by omega,
      show ¬ (m + 11 = 7) by omega,
      show ¬ (m + 11 = 8) by omega,
      show ¬ (m + 11 = 9) by omega,
      show ¬ (m + 11 = 10) by omega, if_true, if_false]
    rw [a_poly (m + 11), a_poly (m + 10), a_poly (m + 9), a_poly (m + 8), a_poly (m + 7), a_poly (m + 6), a_poly (m + 5), a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1)]
    push_cast
    ring

/-- Barker's recurrence. -/
theorem recur : ∀ n : ℕ, 10 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
  rw [show m + 11 - 1 = m + 10 by omega, show m + 11 - 2 = m + 9 by omega, show m + 11 - 3 = m + 8 by omega, show m + 11 - 4 = m + 7 by omega, show m + 11 - 5 = m + 6 by omega, show m + 11 - 6 = m + 5 by omega, show m + 11 - 7 = m + 4 by omega, show m + 11 - 8 = m + 3 by omega, show m + 11 - 9 = m + 2 by omega, show m + 11 - 10 = m + 1 by omega]
  have h : (a (m + 11) : ℚ) = 10 * a (m + 10) - 45 * a (m + 9) + 120 * a (m + 8) - 210 * a (m + 7) + 252 * a (m + 6) - 210 * a (m + 5) + 120 * a (m + 4) - 45 * a (m + 3) + 10 * a (m + 2) - a (m + 1) := by
    rw [a_poly (m + 11), a_poly (m + 10), a_poly (m + 9), a_poly (m + 8), a_poly (m + 7), a_poly (m + 6), a_poly (m + 5), a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1)]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (110 + 423 * X - 422 * X ^ 2 - 766 * X ^ 3 + 848 * X ^ 4 - 246 * X ^ 5 + 90 * X ^ 6 - 44 * X ^ 7 + 10 * X ^ 8 - X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a200877

theorem OMA.solution : type_of% @OMA.S_oeis_a200877.main :=
  OMA.S_oeis_a200877.conjecture
