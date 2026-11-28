import OMAStatements.S_oeis_a200841

/-!
OEIS A200841 (R. H. Hardin, Nov 23 2011): Number of 0..n arrays x(0..5) of 6 elements without any two consecutive increases or two consecutive decreases.
Conjectures from Colin Barker, Oct 14 2017: G.f.: x*(64 + 81*x - 3*x^2 - 36*x^3 + 22*x^4 - 7*x^5 + x^6) / (1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.

Proof. An array over Fin N is the increasing enumeration of its j-element value set composed with
a surjection onto Fin j, and the condition only compares entries, so it holds for the array exactly
when it holds for the surjection (`rank_decomp`): a(n) = sum_j C(n + 1, j) c_j, with c_j the number
of valid surjections Fin 6 -> Fin j. The same identity with Fin q in place of Fin (n + 1) gives
b_q = sum_j C(q, j) c_j for the number b_q of valid arrays over Fin q; kernel-checked transfer
tables over the last two entries give b_1..b_6, and triangular elimination gives the c_j
(`c_vals`). So a(n) is an explicit polynomial of degree 6 (`a_poly`), and the g.f. and the
recurrence follow by comparing coefficients.
-/

namespace OMA.S_oeis_a200841

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
def Rel (x y z : ℕ) : Prop := ¬ (x < y ∧ y < z) ∧ ¬ (x > y ∧ y > z)

instance (x y z : ℕ) : Decidable (Rel x y z) := by unfold Rel; infer_instance

lemma rel_inv : ∀ f : ℕ → ℕ, StrictMono f → ∀ x y z, Rel (f x) (f y) (f z) ↔ Rel x y z := by
  intro f hf x y z
  simp only [Rel, gt_iff_lt, hf.lt_iff_lt]

lemma win_inv : ∀ f : ℕ → ℕ, StrictMono f → ∀ y : Fin 6 → ℕ, Win Rel (f ∘ y) ↔ Win Rel y :=
  win_inv_of Rel rel_inv

/-- The count over Fin q. -/
def bc (q : ℕ) : ℕ :=
  ((univ : Finset (Fin 6 → Fin q)).filter (fun x => Win Rel (fun i => (x i : ℕ)))).card

/-- Transfer table over Fin 1: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T1 : Fin 5 → Fin 1 → Fin 1 → ℕ :=
  ![![![1]], ![![1]], ![![1]], ![![1]], ![![1]]]

/-- Transfer table over Fin 2: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T2 : Fin 5 → Fin 2 → Fin 2 → ℕ :=
  ![![![1, 1], ![1, 1]], ![![2, 2], ![2, 2]], ![![4, 4], ![4, 4]], ![![8, 8], ![8, 8]], ![![16, 16], ![16, 16]]]

/-- Transfer table over Fin 3: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T3 : Fin 5 → Fin 3 → Fin 3 → ℕ :=
  ![![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]], ![![3, 2, 3], ![3, 3, 3], ![3, 2, 3]], ![![8, 6, 8], ![8, 9, 8], ![8, 6, 8]], ![![22, 17, 22], ![22, 25, 22], ![22, 17, 22]], ![![61, 47, 61], ![61, 69, 61], ![61, 47, 61]]]

/-- Transfer table over Fin 4: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T4 : Fin 5 → Fin 4 → Fin 4 → ℕ :=
  ![![![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1]], ![![4, 2, 3, 4], ![4, 4, 3, 4], ![4, 3, 4, 4], ![4, 3, 2, 4]], ![![13, 8, 11, 13], ![13, 15, 11, 13], ![13, 11, 15, 13], ![13, 11, 8, 13]], ![![45, 28, 39, 45], ![45, 52, 39, 45], ![45, 39, 52, 45], ![45, 39, 28, 45]], ![![157, 97, 136, 157], ![157, 181, 136, 157], ![157, 136, 181, 157], ![157, 136, 97, 157]]]

/-- Transfer table over Fin 5: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T5 : Fin 5 → Fin 5 → Fin 5 → ℕ :=
  ![![![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1]], ![![5, 2, 3, 4, 5], ![5, 5, 3, 4, 5], ![5, 4, 5, 4, 5], ![5, 4, 3, 5, 5], ![5, 4, 3, 2, 5]], ![![19, 10, 14, 17, 19], ![19, 22, 14, 17, 19], ![19, 17, 23, 17, 19], ![19, 17, 14, 22, 19], ![19, 17, 14, 10, 19]], ![![79, 41, 59, 72, 79], ![79, 91, 59, 72, 79], ![79, 72, 95, 72, 79], ![79, 72, 59, 91, 79], ![79, 72, 59, 41, 79]], ![![330, 170, 246, 301, 330], ![330, 380, 246, 301, 330], ![330, 301, 397, 301, 330], ![330, 301, 246, 380, 330], ![330, 301, 246, 170, 330]]]

/-- Transfer table over Fin 6: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T6 : Fin 5 → Fin 6 → Fin 6 → ℕ :=
  ![![![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1]], ![![6, 2, 3, 4, 5, 6], ![6, 6, 3, 4, 5, 6], ![6, 5, 6, 4, 5, 6], ![6, 5, 4, 6, 5, 6], ![6, 5, 4, 3, 6, 6], ![6, 5, 4, 3, 2, 6]], ![![26, 12, 17, 21, 24, 26], ![26, 30, 17, 21, 24, 26], ![26, 24, 32, 21, 24, 26], ![26, 24, 21, 32, 24, 26], ![26, 24, 21, 17, 30, 26], ![26, 24, 21, 17, 12, 26]], ![![126, 56, 82, 103, 118, 126], ![126, 144, 82, 103, 118, 126], ![126, 118, 153, 103, 118, 126], ![126, 118, 103, 153, 118, 126], ![126, 118, 103, 82, 144, 126], ![126, 118, 103, 82, 56, 126]], ![![611, 270, 397, 500, 573, 611], ![611, 699, 397, 500, 573, 611], ![611, 573, 744, 500, 573, 611], ![611, 573, 500, 744, 573, 611], ![611, 573, 500, 397, 699, 611], ![611, 573, 500, 397, 270, 611]]]

theorem check_all :
    ((∀ u v : Fin 1, T1 0 u v = 1) ∧
      (∀ m : Fin 4, ∀ u v : Fin 1, T1 m.succ u v =
        ∑ w : Fin 1, if Rel u v w then T1 m.castSucc v w else 0) ∧
      ∑ u : Fin 1, ∑ v : Fin 1, T1 (Fin.last 4) u v = 1) ∧
    ((∀ u v : Fin 2, T2 0 u v = 1) ∧
      (∀ m : Fin 4, ∀ u v : Fin 2, T2 m.succ u v =
        ∑ w : Fin 2, if Rel u v w then T2 m.castSucc v w else 0) ∧
      ∑ u : Fin 2, ∑ v : Fin 2, T2 (Fin.last 4) u v = 64) ∧
    ((∀ u v : Fin 3, T3 0 u v = 1) ∧
      (∀ m : Fin 4, ∀ u v : Fin 3, T3 m.succ u v =
        ∑ w : Fin 3, if Rel u v w then T3 m.castSucc v w else 0) ∧
      ∑ u : Fin 3, ∑ v : Fin 3, T3 (Fin.last 4) u v = 529) ∧
    ((∀ u v : Fin 4, T4 0 u v = 1) ∧
      (∀ m : Fin 4, ∀ u v : Fin 4, T4 m.succ u v =
        ∑ w : Fin 4, if Rel u v w then T4 m.castSucc v w else 0) ∧
      ∑ u : Fin 4, ∑ v : Fin 4, T4 (Fin.last 4) u v = 2356) ∧
    ((∀ u v : Fin 5, T5 0 u v = 1) ∧
      (∀ m : Fin 4, ∀ u v : Fin 5, T5 m.succ u v =
        ∑ w : Fin 5, if Rel u v w then T5 m.castSucc v w else 0) ∧
      ∑ u : Fin 5, ∑ v : Fin 5, T5 (Fin.last 4) u v = 7587) ∧
    ((∀ u v : Fin 6, T6 0 u v = 1) ∧
      (∀ m : Fin 4, ∀ u v : Fin 6, T6 m.succ u v =
        ∑ w : Fin 6, if Rel u v w then T6 m.castSucc v w else 0) ∧
      ∑ u : Fin 6, ∑ v : Fin 6, T6 (Fin.last 4) u v = 19930) := by
  decide +kernel

/-- The triangular system for the c_j, over an arbitrary function (kept apart from surjCount, whose
values the kernel would otherwise compute when it compares terms). -/
lemma solve (s : ℕ → ℕ)
    (e0 : 0 = ∑ j ∈ range 7, (0 : ℕ).choose j * s j)
    (e1 : 1 = ∑ j ∈ range 7, (1 : ℕ).choose j * s j)
    (e2 : 64 = ∑ j ∈ range 7, (2 : ℕ).choose j * s j)
    (e3 : 529 = ∑ j ∈ range 7, (3 : ℕ).choose j * s j)
    (e4 : 2356 = ∑ j ∈ range 7, (4 : ℕ).choose j * s j)
    (e5 : 7587 = ∑ j ∈ range 7, (5 : ℕ).choose j * s j)
    (e6 : 19930 = ∑ j ∈ range 7, (6 : ℕ).choose j * s j) :
    s 0 = 0 ∧ s 1 = 1 ∧ s 2 = 62 ∧ s 3 = 340 ∧ s 4 = 620 ∧ s 5 = 462 ∧ s 6 = 122 := by
  simp only [sum_range_succ, sum_range_zero, zero_add, one_mul, zero_mul, add_zero,
    show (0 : ℕ).choose 0 = 1 by decide, show (0 : ℕ).choose 1 = 0 by decide, show (0 : ℕ).choose 2 = 0 by decide, show (0 : ℕ).choose 3 = 0 by decide, show (0 : ℕ).choose 4 = 0 by decide, show (0 : ℕ).choose 5 = 0 by decide, show (0 : ℕ).choose 6 = 0 by decide,
    show (1 : ℕ).choose 0 = 1 by decide, show (1 : ℕ).choose 1 = 1 by decide, show (1 : ℕ).choose 2 = 0 by decide, show (1 : ℕ).choose 3 = 0 by decide, show (1 : ℕ).choose 4 = 0 by decide, show (1 : ℕ).choose 5 = 0 by decide, show (1 : ℕ).choose 6 = 0 by decide,
    show (2 : ℕ).choose 0 = 1 by decide, show (2 : ℕ).choose 1 = 2 by decide, show (2 : ℕ).choose 2 = 1 by decide, show (2 : ℕ).choose 3 = 0 by decide, show (2 : ℕ).choose 4 = 0 by decide, show (2 : ℕ).choose 5 = 0 by decide, show (2 : ℕ).choose 6 = 0 by decide,
    show (3 : ℕ).choose 0 = 1 by decide, show (3 : ℕ).choose 1 = 3 by decide, show (3 : ℕ).choose 2 = 3 by decide, show (3 : ℕ).choose 3 = 1 by decide, show (3 : ℕ).choose 4 = 0 by decide, show (3 : ℕ).choose 5 = 0 by decide, show (3 : ℕ).choose 6 = 0 by decide,
    show (4 : ℕ).choose 0 = 1 by decide, show (4 : ℕ).choose 1 = 4 by decide, show (4 : ℕ).choose 2 = 6 by decide, show (4 : ℕ).choose 3 = 4 by decide, show (4 : ℕ).choose 4 = 1 by decide, show (4 : ℕ).choose 5 = 0 by decide, show (4 : ℕ).choose 6 = 0 by decide,
    show (5 : ℕ).choose 0 = 1 by decide, show (5 : ℕ).choose 1 = 5 by decide, show (5 : ℕ).choose 2 = 10 by decide, show (5 : ℕ).choose 3 = 10 by decide, show (5 : ℕ).choose 4 = 5 by decide, show (5 : ℕ).choose 5 = 1 by decide, show (5 : ℕ).choose 6 = 0 by decide,
    show (6 : ℕ).choose 0 = 1 by decide, show (6 : ℕ).choose 1 = 6 by decide, show (6 : ℕ).choose 2 = 15 by decide, show (6 : ℕ).choose 3 = 20 by decide, show (6 : ℕ).choose 4 = 15 by decide, show (6 : ℕ).choose 5 = 6 by decide, show (6 : ℕ).choose 6 = 1 by decide] at e0 e1 e2 e3 e4 e5 e6
  omega

lemma c_vals : surjCount (Win Rel (L := 6)) 0 = 0 ∧ surjCount (Win Rel (L := 6)) 1 = 1 ∧ surjCount (Win Rel (L := 6)) 2 = 62 ∧ surjCount (Win Rel (L := 6)) 3 = 340 ∧ surjCount (Win Rel (L := 6)) 4 = 620 ∧ surjCount (Win Rel (L := 6)) 5 = 462 ∧ surjCount (Win Rel (L := 6)) 6 = 122 := by
  have hb1 : bc 1 = 1 := by
    have h := check_all.1
    exact (b_val Rel T1 h.1 h.2.1).trans h.2.2
  have hb2 : bc 2 = 64 := by
    have h := check_all.2.1
    exact (b_val Rel T2 h.1 h.2.1).trans h.2.2
  have hb3 : bc 3 = 529 := by
    have h := check_all.2.2.1
    exact (b_val Rel T3 h.1 h.2.1).trans h.2.2
  have hb4 : bc 4 = 2356 := by
    have h := check_all.2.2.2.1
    exact (b_val Rel T4 h.1 h.2.1).trans h.2.2
  have hb5 : bc 5 = 7587 := by
    have h := check_all.2.2.2.2.1
    exact (b_val Rel T5 h.1 h.2.1).trans h.2.2
  have hb6 : bc 6 = 19930 := by
    have h := check_all.2.2.2.2.2
    exact (b_val Rel T6 h.1 h.2.1).trans h.2.2
  have e0 : bc 0 = ∑ j ∈ range 7, (0 : ℕ).choose j * surjCount (Win Rel (L := 6)) j :=
    rank_decomp (Win Rel (L := 6)) win_inv 0
  have e1 : bc 1 = ∑ j ∈ range 7, (1 : ℕ).choose j * surjCount (Win Rel (L := 6)) j :=
    rank_decomp (Win Rel (L := 6)) win_inv 1
  have e2 : bc 2 = ∑ j ∈ range 7, (2 : ℕ).choose j * surjCount (Win Rel (L := 6)) j :=
    rank_decomp (Win Rel (L := 6)) win_inv 2
  have e3 : bc 3 = ∑ j ∈ range 7, (3 : ℕ).choose j * surjCount (Win Rel (L := 6)) j :=
    rank_decomp (Win Rel (L := 6)) win_inv 3
  have e4 : bc 4 = ∑ j ∈ range 7, (4 : ℕ).choose j * surjCount (Win Rel (L := 6)) j :=
    rank_decomp (Win Rel (L := 6)) win_inv 4
  have e5 : bc 5 = ∑ j ∈ range 7, (5 : ℕ).choose j * surjCount (Win Rel (L := 6)) j :=
    rank_decomp (Win Rel (L := 6)) win_inv 5
  have e6 : bc 6 = ∑ j ∈ range 7, (6 : ℕ).choose j * surjCount (Win Rel (L := 6)) j :=
    rank_decomp (Win Rel (L := 6)) win_inv 6
  have hb0 : bc 0 = 0 := (b_eq Rel 0 4).trans (by simp)
  exact solve _ (hb0.symm.trans e0) (hb1.symm.trans e1) (hb2.symm.trans e2) (hb3.symm.trans e3) (hb4.symm.trans e4) (hb5.symm.trans e5) (hb6.symm.trans e6)

lemma a_sum (n : ℕ) : (a n : ℚ) = ∑ j ∈ range 7, (((n + 1).choose j : ℕ) : ℚ) *
    (surjCount (Win Rel (L := 6)) j : ℚ) := by
  have h := rank_decomp (Win Rel (L := 6)) win_inv (n + 1)
  have ha : a n = ((univ : Finset (Fin 6 → Fin (n + 1))).filter
      (fun x => Win Rel (fun i => (x i : ℕ)))).card := by
    unfold a
    exact congrArg Finset.card (filter_congr (fun x _ => Iff.rfl))
  rw [ha, h]
  simp only [Nat.cast_sum, Nat.cast_mul]

/-- a(n) as a polynomial in n. -/
lemma a_poly (n : ℕ) : (a n : ℚ) = 1 + (239 / 30) * (n : ℚ) + (1801 / 90) * (n : ℚ) ^ 2 + (521 / 24) * (n : ℚ) ^ 3 + (779 / 72) * (n : ℚ) ^ 4 + (93 / 40) * (n : ℚ) ^ 5 + (61 / 360) * (n : ℚ) ^ 6 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := c_vals
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero, choose_q, prod_range_succ, prod_range_zero,
    c0, c1, c2, c3, c4, c5, c6, Nat.factorial]
  push_cast
  ring

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (64 + 81 * X - 3 * X ^ 2 - 36 * X ^ 3 + 22 * X ^ 4 - 7 * X ^ 5 + X ^ 6) := by
  have v1 : (a 1 : ℚ) = 64 := by rw [a_poly]; norm_num
  have v2 : (a 2 : ℚ) = 529 := by rw [a_poly]; norm_num
  have v3 : (a 3 : ℚ) = 2356 := by rw [a_poly]; norm_num
  have v4 : (a 4 : ℚ) = 7587 := by rw [a_poly]; norm_num
  have v5 : (a 5 : ℚ) = 19930 := by rw [a_poly]; norm_num
  have v6 : (a 6 : ℚ) = 45465 := by rw [a_poly]; norm_num
  have v7 : (a 7 : ℚ) = 93472 := by rw [a_poly]; norm_num
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 7 = A - C (7 : ℚ) * (A * X ^ 1) + C (21 : ℚ) * (A * X ^ 2) - C (35 : ℚ) * (A * X ^ 3) + C (35 : ℚ) * (A * X ^ 4) - C (21 : ℚ) * (A * X ^ 5) + C (7 : ℚ) * (A * X ^ 6) - A * X ^ 7 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (64 + 81 * X - 3 * X ^ 2 - 36 * X ^ 3 + 22 * X ^ 4 - 7 * X ^ 5 + X ^ 6) : ℚ⟦X⟧) = X ^ 1 * C (64 : ℚ) + X ^ 2 * C (81 : ℚ) - X ^ 3 * C (3 : ℚ) - X ^ 4 * C (36 : ℚ) + X ^ 5 * C (22 : ℚ) - X ^ 6 * C (7 : ℚ) + X ^ 7 := by
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
      show ¬ (m + 8 - 1 = 0) by omega,
      show m + 8 - 1 = m + 7 by omega,
      show 2 ≤ m + 8 by omega,
      show ¬ (m + 8 - 2 = 0) by omega,
      show m + 8 - 2 = m + 6 by omega,
      show 3 ≤ m + 8 by omega,
      show ¬ (m + 8 - 3 = 0) by omega,
      show m + 8 - 3 = m + 5 by omega,
      show 4 ≤ m + 8 by omega,
      show ¬ (m + 8 - 4 = 0) by omega,
      show m + 8 - 4 = m + 4 by omega,
      show 5 ≤ m + 8 by omega,
      show ¬ (m + 8 - 5 = 0) by omega,
      show m + 8 - 5 = m + 3 by omega,
      show 6 ≤ m + 8 by omega,
      show ¬ (m + 8 - 6 = 0) by omega,
      show m + 8 - 6 = m + 2 by omega,
      show 7 ≤ m + 8 by omega,
      show ¬ (m + 8 - 7 = 0) by omega,
      show m + 8 - 7 = m + 1 by omega,
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
      X * (64 + 81 * X - 3 * X ^ 2 - 36 * X ^ 3 + 22 * X ^ 4 - 7 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a200841

theorem OMA.solution : type_of% @OMA.S_oeis_a200841.main :=
  OMA.S_oeis_a200841.conjecture
