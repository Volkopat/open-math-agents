import OMAStatements.S_oeis_a200844

/-!
OEIS A200844 (R. H. Hardin, Nov 23 2011): Number of 0..n arrays x(0..8) of 9 elements without any two consecutive increases or two consecutive decreases.
Conjectures from Colin Barker, Oct 14 2017: G.f.: x*(512 + 6115*x + 10390*x^2 - 618*x^3 - 622*x^4 + 36*x^5 + 94*x^6 - 44*x^7 + 10*x^8 - x^9) / (1 - x)^10. a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n > 10.

Proof. An array over Fin N is the increasing enumeration of its j-element value set composed with
a surjection onto Fin j, and the condition only compares entries, so it holds for the array exactly
when it holds for the surjection (`rank_decomp`): a(n) = sum_j C(n + 1, j) c_j, with c_j the number
of valid surjections Fin 9 -> Fin j. The same identity with Fin q in place of Fin (n + 1) gives
b_q = sum_j C(q, j) c_j for the number b_q of valid arrays over Fin q; kernel-checked transfer
tables over the last two entries give b_1..b_9, and triangular elimination gives the c_j
(`c_vals`). So a(n) is an explicit polynomial of degree 9 (`a_poly`), and the g.f. and the
recurrence follow by comparing coefficients.
-/

namespace OMA.S_oeis_a200844

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
  ![![![1, 1], ![1, 1]], ![![2, 2], ![2, 2]], ![![4, 4], ![4, 4]], ![![8, 8], ![8, 8]], ![![16, 16], ![16, 16]], ![![32, 32], ![32, 32]], ![![64, 64], ![64, 64]], ![![128, 128], ![128, 128]]]

/-- Transfer table over Fin 3: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T3 : Fin 8 → Fin 3 → Fin 3 → ℕ :=
  ![![![1, 1, 1], ![1, 1, 1], ![1, 1, 1]], ![![3, 2, 3], ![3, 3, 3], ![3, 2, 3]], ![![8, 6, 8], ![8, 9, 8], ![8, 6, 8]], ![![22, 17, 22], ![22, 25, 22], ![22, 17, 22]], ![![61, 47, 61], ![61, 69, 61], ![61, 47, 61]], ![![169, 130, 169], ![169, 191, 169], ![169, 130, 169]], ![![468, 360, 468], ![468, 529, 468], ![468, 360, 468]], ![![1296, 997, 1296], ![1296, 1465, 1296], ![1296, 997, 1296]]]

/-- Transfer table over Fin 4: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T4 : Fin 8 → Fin 4 → Fin 4 → ℕ :=
  ![![![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 1]], ![![4, 2, 3, 4], ![4, 4, 3, 4], ![4, 3, 4, 4], ![4, 3, 2, 4]], ![![13, 8, 11, 13], ![13, 15, 11, 13], ![13, 11, 15, 13], ![13, 11, 8, 13]], ![![45, 28, 39, 45], ![45, 52, 39, 45], ![45, 39, 52, 45], ![45, 39, 28, 45]], ![![157, 97, 136, 157], ![157, 181, 136, 157], ![157, 136, 181, 157], ![157, 136, 97, 157]], ![![547, 338, 474, 547], ![547, 631, 474, 547], ![547, 474, 631, 547], ![547, 474, 338, 547]], ![![1906, 1178, 1652, 1906], ![1906, 2199, 1652, 1906], ![1906, 1652, 2199, 1906], ![1906, 1652, 1178, 1906]], ![![6642, 4105, 5757, 6642], ![6642, 7663, 5757, 6642], ![6642, 5757, 7663, 6642], ![6642, 5757, 4105, 6642]]]

/-- Transfer table over Fin 5: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T5 : Fin 8 → Fin 5 → Fin 5 → ℕ :=
  ![![![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1], ![1, 1, 1, 1, 1]], ![![5, 2, 3, 4, 5], ![5, 5, 3, 4, 5], ![5, 4, 5, 4, 5], ![5, 4, 3, 5, 5], ![5, 4, 3, 2, 5]], ![![19, 10, 14, 17, 19], ![19, 22, 14, 17, 19], ![19, 17, 23, 17, 19], ![19, 17, 14, 22, 19], ![19, 17, 14, 10, 19]], ![![79, 41, 59, 72, 79], ![79, 91, 59, 72, 79], ![79, 72, 95, 72, 79], ![79, 72, 59, 91, 79], ![79, 72, 59, 41, 79]], ![![330, 170, 246, 301, 330], ![330, 380, 246, 301, 330], ![330, 301, 397, 301, 330], ![330, 301, 246, 380, 330], ![330, 301, 246, 170, 330]], ![![1377, 710, 1028, 1257, 1377], ![1377, 1587, 1028, 1257, 1377], ![1377, 1257, 1659, 1257, 1377], ![1377, 1257, 1028, 1587, 1377], ![1377, 1257, 1028, 710, 1377]], ![![5749, 2964, 4293, 5249, 5749], ![5749, 6626, 4293, 5249, 5749], ![5749, 5249, 6927, 5249, 5749], ![5749, 5249, 4293, 6626, 5749], ![5749, 5249, 4293, 2964, 5749]], ![![24004, 12375, 17925, 21917, 24004], ![24004, 27666, 17925, 21917, 24004], ![24004, 21917, 28923, 21917, 24004], ![24004, 21917, 17925, 27666, 24004], ![24004, 21917, 17925, 12375, 24004]]]

/-- Transfer table over Fin 6: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T6 : Fin 8 → Fin 6 → Fin 6 → ℕ :=
  ![![![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1]], ![![6, 2, 3, 4, 5, 6], ![6, 6, 3, 4, 5, 6], ![6, 5, 6, 4, 5, 6], ![6, 5, 4, 6, 5, 6], ![6, 5, 4, 3, 6, 6], ![6, 5, 4, 3, 2, 6]], ![![26, 12, 17, 21, 24, 26], ![26, 30, 17, 21, 24, 26], ![26, 24, 32, 21, 24, 26], ![26, 24, 21, 32, 24, 26], ![26, 24, 21, 17, 30, 26], ![26, 24, 21, 17, 12, 26]], ![![126, 56, 82, 103, 118, 126], ![126, 144, 82, 103, 118, 126], ![126, 118, 153, 103, 118, 126], ![126, 118, 103, 153, 118, 126], ![126, 118, 103, 82, 144, 126], ![126, 118, 103, 82, 56, 126]], ![![611, 270, 397, 500, 573, 611], ![611, 699, 397, 500, 573, 611], ![611, 573, 744, 500, 573, 611], ![611, 573, 500, 744, 573, 611], ![611, 573, 500, 397, 699, 611], ![611, 573, 500, 397, 270, 611]], ![![2962, 1310, 1928, 2428, 2780, 2962], ![2962, 3391, 1928, 2428, 2780, 2962], ![2962, 2780, 3612, 2428, 2780, 2962], ![2962, 2780, 2428, 3612, 2780, 2962], ![2962, 2780, 2428, 1928, 3391, 2962], ![2962, 2780, 2428, 1928, 1310, 2962]], ![![14370, 6353, 9354, 11782, 13489, 14370], ![14370, 16451, 9354, 11782, 13489, 14370], ![14370, 13489, 17524, 11782, 13489, 14370], ![14370, 13489, 11782, 17524, 13489, 14370], ![14370, 13489, 11782, 9354, 16451, 14370], ![14370, 13489, 11782, 9354, 6353, 14370]], ![![69718, 30821, 45383, 57165, 65446, 69718], ![69718, 79816, 45383, 57165, 65446, 69718], ![69718, 65446, 85024, 57165, 65446, 69718], ![69718, 65446, 57165, 85024, 65446, 69718], ![69718, 65446, 57165, 45383, 79816, 69718], ![69718, 65446, 57165, 45383, 30821, 69718]]]

/-- Transfer table over Fin 7: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T7 : Fin 8 → Fin 7 → Fin 7 → ℕ :=
  ![![![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1]], ![![7, 2, 3, 4, 5, 6, 7], ![7, 7, 3, 4, 5, 6, 7], ![7, 6, 7, 4, 5, 6, 7], ![7, 6, 5, 7, 5, 6, 7], ![7, 6, 5, 4, 7, 6, 7], ![7, 6, 5, 4, 3, 7, 7], ![7, 6, 5, 4, 3, 2, 7]], ![![34, 14, 20, 25, 29, 32, 34], ![34, 39, 20, 25, 29, 32, 34], ![34, 32, 42, 25, 29, 32, 34], ![34, 32, 29, 43, 29, 32, 34], ![34, 32, 29, 25, 42, 32, 34], ![34, 32, 29, 25, 20, 39, 34], ![34, 32, 29, 25, 20, 14, 34]], ![![188, 73, 108, 138, 162, 179, 188], ![188, 213, 108, 138, 162, 179, 188], ![188, 179, 228, 138, 162, 179, 188], ![188, 179, 162, 233, 162, 179, 188], ![188, 179, 162, 138, 228, 179, 188], ![188, 179, 162, 138, 108, 213, 188], ![188, 179, 162, 138, 108, 73, 188]], ![![1036, 401, 595, 762, 895, 988, 1036], ![1036, 1176, 595, 762, 895, 988, 1036], ![1036, 988, 1262, 762, 895, 988, 1036], ![1036, 988, 895, 1291, 895, 988, 1036], ![1036, 988, 895, 762, 1262, 988, 1036], ![1036, 988, 895, 762, 595, 1176, 1036], ![1036, 988, 895, 762, 595, 401, 1036]], ![![5713, 2212, 3286, 4210, 4943, 5452, 5713], ![5713, 6488, 3286, 4210, 4943, 5452, 5713], ![5713, 5452, 6967, 4210, 4943, 5452, 5713], ![5713, 5452, 4943, 7129, 4943, 5452, 5713], ![5713, 5452, 4943, 4210, 6967, 5452, 5713], ![5713, 5452, 4943, 4210, 3286, 6488, 5713], ![5713, 5452, 4943, 4210, 3286, 2212, 5713]], ![![31529, 12201, 18132, 23237, 27285, 30092, 31529], ![31529, 35805, 18132, 23237, 27285, 30092, 31529], ![31529, 30092, 38450, 23237, 27285, 30092, 31529], ![31529, 30092, 27285, 39345, 27285, 30092, 31529], ![31529, 30092, 27285, 23237, 38450, 30092, 31529], ![31529, 30092, 27285, 23237, 18132, 35805, 31529], ![31529, 30092, 27285, 23237, 18132, 12201, 31529]], ![![174005, 67334, 100071, 128251, 150593, 166080, 174005], ![174005, 197609, 100071, 128251, 150593, 166080, 174005], ![174005, 166080, 212214, 128251, 150593, 166080, 174005], ![174005, 166080, 150593, 217157, 150593, 166080, 174005], ![174005, 166080, 150593, 128251, 212214, 166080, 174005], ![174005, 166080, 150593, 128251, 100071, 197609, 174005], ![174005, 166080, 150593, 128251, 100071, 67334, 174005]]]

/-- Transfer table over Fin 8: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T8 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1]], ![![8, 2, 3, 4, 5, 6, 7, 8], ![8, 8, 3, 4, 5, 6, 7, 8], ![8, 7, 8, 4, 5, 6, 7, 8], ![8, 7, 6, 8, 5, 6, 7, 8], ![8, 7, 6, 5, 8, 6, 7, 8], ![8, 7, 6, 5, 4, 8, 7, 8], ![8, 7, 6, 5, 4, 3, 8, 8], ![8, 7, 6, 5, 4, 3, 2, 8]], ![![43, 16, 23, 29, 34, 38, 41, 43], ![43, 49, 23, 29, 34, 38, 41, 43], ![43, 41, 53, 29, 34, 38, 41, 43], ![43, 41, 38, 55, 34, 38, 41, 43], ![43, 41, 38, 34, 55, 38, 41, 43], ![43, 41, 38, 34, 29, 53, 41, 43], ![43, 41, 38, 34, 29, 23, 49, 43], ![43, 41, 38, 34, 29, 23, 16, 43]], ![![267, 92, 137, 177, 211, 238, 257, 267], ![267, 300, 137, 177, 211, 238, 257, 267], ![267, 257, 322, 177, 211, 238, 257, 267], ![267, 257, 238, 333, 211, 238, 257, 267], ![267, 257, 238, 211, 333, 238, 257, 267], ![267, 257, 238, 211, 177, 322, 257, 267], ![267, 257, 238, 211, 177, 137, 300, 267], ![267, 257, 238, 211, 177, 137, 92, 267]], ![![1646, 567, 846, 1095, 1306, 1472, 1587, 1646], ![1646, 1854, 846, 1095, 1306, 1472, 1587, 1646], ![1646, 1587, 1996, 1095, 1306, 1472, 1587, 1646], ![1646, 1587, 1472, 2068, 1306, 1472, 1587, 1646], ![1646, 1587, 1472, 1306, 2068, 1472, 1587, 1646], ![1646, 1587, 1472, 1306, 1095, 1996, 1587, 1646], ![1646, 1587, 1472, 1306, 1095, 846, 1854, 1646], ![1646, 1587, 1472, 1306, 1095, 846, 567, 1646]], ![![10165, 3500, 5229, 6773, 8079, 9102, 9806, 10165], ![10165, 11452, 5229, 6773, 8079, 9102, 9806, 10165], ![10165, 9806, 12335, 6773, 8079, 9102, 9806, 10165], ![10165, 9806, 9102, 12784, 8079, 9102, 9806, 10165], ![10165, 9806, 9102, 8079, 12784, 9102, 9806, 10165], ![10165, 9806, 9102, 8079, 6773, 12335, 9806, 10165], ![10165, 9806, 9102, 8079, 6773, 5229, 11452, 10165], ![10165, 9806, 9102, 8079, 6773, 5229, 3500, 10165]], ![![62819, 21617, 32306, 41857, 49936, 56260, 60606, 62819], ![62819, 70771, 32306, 41857, 49936, 56260, 60606, 62819], ![62819, 60606, 76231, 41857, 49936, 56260, 60606, 62819], ![62819, 60606, 56260, 79009, 49936, 56260, 60606, 62819], ![62819, 60606, 56260, 49936, 79009, 56260, 60606, 62819], ![62819, 60606, 56260, 49936, 41857, 76231, 60606, 62819], ![62819, 60606, 56260, 49936, 41857, 32306, 70771, 62819], ![62819, 60606, 56260, 49936, 41857, 32306, 21617, 62819]], ![![388220, 133590, 199656, 258694, 308630, 347709, 374555, 388220], ![388220, 437374, 199656, 258694, 308630, 347709, 374555, 388220], ![388220, 374555, 471134, 258694, 308630, 347709, 374555, 388220], ![388220, 374555, 347709, 488315, 308630, 347709, 374555, 388220], ![388220, 374555, 347709, 308630, 488315, 347709, 374555, 388220], ![388220, 374555, 347709, 308630, 258694, 471134, 374555, 388220], ![388220, 374555, 347709, 308630, 258694, 199656, 437374, 388220], ![388220, 374555, 347709, 308630, 258694, 199656, 133590, 388220]]]

/-- Transfer table over Fin 9: entry m, u, v counts the arrays of length m + 2 starting
u, v. -/
def T9 : Fin 8 → Fin 9 → Fin 9 → ℕ :=
  ![![![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1, 1]], ![![9, 2, 3, 4, 5, 6, 7, 8, 9], ![9, 9, 3, 4, 5, 6, 7, 8, 9], ![9, 8, 9, 4, 5, 6, 7, 8, 9], ![9, 8, 7, 9, 5, 6, 7, 8, 9], ![9, 8, 7, 6, 9, 6, 7, 8, 9], ![9, 8, 7, 6, 5, 9, 7, 8, 9], ![9, 8, 7, 6, 5, 4, 9, 8, 9], ![9, 8, 7, 6, 5, 4, 3, 9, 9], ![9, 8, 7, 6, 5, 4, 3, 2, 9]], ![![53, 18, 26, 33, 39, 44, 48, 51, 53], ![53, 60, 26, 33, 39, 44, 48, 51, 53], ![53, 51, 65, 33, 39, 44, 48, 51, 53], ![53, 51, 48, 68, 39, 44, 48, 51, 53], ![53, 51, 48, 44, 69, 44, 48, 51, 53], ![53, 51, 48, 44, 39, 68, 48, 51, 53], ![53, 51, 48, 44, 39, 33, 65, 51, 53], ![53, 51, 48, 44, 39, 33, 26, 60, 53], ![53, 51, 48, 44, 39, 33, 26, 18, 53]], ![![365, 113, 169, 220, 265, 303, 333, 354, 365], ![365, 407, 169, 220, 265, 303, 333, 354, 365], ![365, 354, 437, 220, 265, 303, 333, 354, 365], ![365, 354, 333, 455, 265, 303, 333, 354, 365], ![365, 354, 333, 303, 461, 303, 333, 354, 365], ![365, 354, 333, 303, 265, 455, 333, 354, 365], ![365, 354, 333, 303, 265, 220, 437, 354, 365], ![365, 354, 333, 303, 265, 220, 169, 407, 365], ![365, 354, 333, 303, 265, 220, 169, 113, 365]], ![![2487, 772, 1156, 1507, 1816, 2075, 2277, 2416, 2487], ![2487, 2781, 1156, 1507, 1816, 2075, 2277, 2416, 2487], ![2487, 2416, 2996, 1507, 1816, 2075, 2277, 2416, 2487], ![2487, 2416, 2277, 3127, 1816, 2075, 2277, 2416, 2487], ![2487, 2416, 2277, 2075, 3171, 2075, 2277, 2416, 2487], ![2487, 2416, 2277, 2075, 1816, 3127, 2277, 2416, 2487], ![2487, 2416, 2277, 2075, 1816, 1507, 2996, 2416, 2487], ![2487, 2416, 2277, 2075, 1816, 1507, 1156, 2781, 2487], ![2487, 2416, 2277, 2075, 1816, 1507, 1156, 772, 2487]], ![![16993, 5268, 7899, 10307, 12426, 14198, 15574, 16515, 16993], ![16993, 19002, 7899, 10307, 12426, 14198, 15574, 16515, 16993], ![16993, 16515, 20477, 10307, 12426, 14198, 15574, 16515, 16993], ![16993, 16515, 15574, 21378, 12426, 14198, 15574, 16515, 16993], ![16993, 16515, 15574, 14198, 21681, 14198, 15574, 16515, 16993], ![16993, 16515, 15574, 14198, 12426, 21378, 15574, 16515, 16993], ![16993, 16515, 15574, 14198, 12426, 10307, 20477, 16515, 16993], ![16993, 16515, 15574, 14198, 12426, 10307, 7899, 19002, 16993], ![16993, 16515, 15574, 14198, 12426, 10307, 7899, 5268, 16993]], ![![116173, 35995, 53985, 70460, 84961, 97084, 106490, 112914, 116173], ![116173, 129907, 53985, 70460, 84961, 97084, 106490, 112914, 116173], ![116173, 112914, 139998, 70460, 84961, 97084, 106490, 112914, 116173], ![116173, 112914, 106490, 146166, 84961, 97084, 106490, 112914, 116173], ![116173, 112914, 106490, 97084, 148241, 97084, 106490, 112914, 116173], ![116173, 112914, 106490, 97084, 84961, 146166, 106490, 112914, 116173], ![116173, 112914, 106490, 97084, 84961, 70460, 139998, 112914, 116173], ![116173, 112914, 106490, 97084, 84961, 70460, 53985, 129907, 116173], ![116173, 112914, 106490, 97084, 84961, 70460, 53985, 35995, 116173]], ![![794235, 246080, 369085, 481743, 580902, 663788, 728080, 771974, 794235], ![794235, 888147, 369085, 481743, 580902, 663788, 728080, 771974, 794235], ![794235, 771974, 957167, 481743, 580902, 663788, 728080, 771974, 794235], ![794235, 771974, 728080, 999365, 580902, 663788, 728080, 771974, 794235], ![794235, 771974, 728080, 663788, 1013563, 663788, 728080, 771974, 794235], ![794235, 771974, 728080, 663788, 580902, 999365, 728080, 771974, 794235], ![794235, 771974, 728080, 663788, 580902, 481743, 957167, 771974, 794235], ![794235, 771974, 728080, 663788, 580902, 481743, 369085, 888147, 794235], ![794235, 771974, 728080, 663788, 580902, 481743, 369085, 246080, 794235]]]

theorem check_all :
    ((∀ u v : Fin 1, T1 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 1, T1 m.succ u v =
        ∑ w : Fin 1, if Rel u v w then T1 m.castSucc v w else 0) ∧
      ∑ u : Fin 1, ∑ v : Fin 1, T1 (Fin.last 7) u v = 1) ∧
    ((∀ u v : Fin 2, T2 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 2, T2 m.succ u v =
        ∑ w : Fin 2, if Rel u v w then T2 m.castSucc v w else 0) ∧
      ∑ u : Fin 2, ∑ v : Fin 2, T2 (Fin.last 7) u v = 512) ∧
    ((∀ u v : Fin 3, T3 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 3, T3 m.succ u v =
        ∑ w : Fin 3, if Rel u v w then T3 m.castSucc v w else 0) ∧
      ∑ u : Fin 3, ∑ v : Fin 3, T3 (Fin.last 7) u v = 11235) ∧
    ((∀ u v : Fin 4, T4 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 4, T4 m.succ u v =
        ∑ w : Fin 4, if Rel u v w then T4 m.castSucc v w else 0) ∧
      ∑ u : Fin 4, ∑ v : Fin 4, T4 (Fin.last 7) u v = 99700) ∧
    ((∀ u v : Fin 5, T5 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 5, T5 m.succ u v =
        ∑ w : Fin 5, if Rel u v w then T5 m.castSucc v w else 0) ∧
      ∑ u : Fin 5, ∑ v : Fin 5, T5 (Fin.last 7) u v = 552247) ∧
    ((∀ u v : Fin 6, T6 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 6, T6 m.succ u v =
        ∑ w : Fin 6, if Rel u v w then T6 m.castSucc v w else 0) ∧
      ∑ u : Fin 6, ∑ v : Fin 6, T6 (Fin.last 7) u v = 2276028) ∧
    ((∀ u v : Fin 7, T7 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 7, T7 m.succ u v =
        ∑ w : Fin 7, if Rel u v w then T7 m.castSucc v w else 0) ∧
      ∑ u : Fin 7, ∑ v : Fin 7, T7 (Fin.last 7) u v = 7642875) ∧
    ((∀ u v : Fin 8, T8 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 8, T8 m.succ u v =
        ∑ w : Fin 8, if Rel u v w then T8 m.castSucc v w else 0) ∧
      ∑ u : Fin 8, ∑ v : Fin 8, T8 (Fin.last 7) u v = 22063924) ∧
    ((∀ u v : Fin 9, T9 0 u v = 1) ∧
      (∀ m : Fin 7, ∀ u v : Fin 9, T9 m.succ u v =
        ∑ w : Fin 9, if Rel u v w then T9 m.castSucc v w else 0) ∧
      ∑ u : Fin 9, ∑ v : Fin 9, T9 (Fin.last 7) u v = 56687801) := by
  decide +kernel

/-- The triangular system for the c_j, over an arbitrary function (kept apart from surjCount, whose
values the kernel would otherwise compute when it compares terms). -/
lemma solve (s : ℕ → ℕ)
    (e0 : 0 = ∑ j ∈ range 10, (0 : ℕ).choose j * s j)
    (e1 : 1 = ∑ j ∈ range 10, (1 : ℕ).choose j * s j)
    (e2 : 512 = ∑ j ∈ range 10, (2 : ℕ).choose j * s j)
    (e3 : 11235 = ∑ j ∈ range 10, (3 : ℕ).choose j * s j)
    (e4 : 99700 = ∑ j ∈ range 10, (4 : ℕ).choose j * s j)
    (e5 : 552247 = ∑ j ∈ range 10, (5 : ℕ).choose j * s j)
    (e6 : 2276028 = ∑ j ∈ range 10, (6 : ℕ).choose j * s j)
    (e7 : 7642875 = ∑ j ∈ range 10, (7 : ℕ).choose j * s j)
    (e8 : 22063924 = ∑ j ∈ range 10, (8 : ℕ).choose j * s j)
    (e9 : 56687801 = ∑ j ∈ range 10, (9 : ℕ).choose j * s j) :
    s 0 = 0 ∧ s 1 = 1 ∧ s 2 = 510 ∧ s 3 = 9702 ∧ s 4 = 57828 ∧ s 5 = 160982 ∧ s 6 = 241020 ∧ s 7 = 200846 ∧ s 8 = 88044 ∧ s 9 = 15872 := by
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

lemma c_vals : surjCount (Win Rel (L := 9)) 0 = 0 ∧ surjCount (Win Rel (L := 9)) 1 = 1 ∧ surjCount (Win Rel (L := 9)) 2 = 510 ∧ surjCount (Win Rel (L := 9)) 3 = 9702 ∧ surjCount (Win Rel (L := 9)) 4 = 57828 ∧ surjCount (Win Rel (L := 9)) 5 = 160982 ∧ surjCount (Win Rel (L := 9)) 6 = 241020 ∧ surjCount (Win Rel (L := 9)) 7 = 200846 ∧ surjCount (Win Rel (L := 9)) 8 = 88044 ∧ surjCount (Win Rel (L := 9)) 9 = 15872 := by
  have hb1 : bc 1 = 1 := by
    have h := check_all.1
    exact (b_val Rel T1 h.1 h.2.1).trans h.2.2
  have hb2 : bc 2 = 512 := by
    have h := check_all.2.1
    exact (b_val Rel T2 h.1 h.2.1).trans h.2.2
  have hb3 : bc 3 = 11235 := by
    have h := check_all.2.2.1
    exact (b_val Rel T3 h.1 h.2.1).trans h.2.2
  have hb4 : bc 4 = 99700 := by
    have h := check_all.2.2.2.1
    exact (b_val Rel T4 h.1 h.2.1).trans h.2.2
  have hb5 : bc 5 = 552247 := by
    have h := check_all.2.2.2.2.1
    exact (b_val Rel T5 h.1 h.2.1).trans h.2.2
  have hb6 : bc 6 = 2276028 := by
    have h := check_all.2.2.2.2.2.1
    exact (b_val Rel T6 h.1 h.2.1).trans h.2.2
  have hb7 : bc 7 = 7642875 := by
    have h := check_all.2.2.2.2.2.2.1
    exact (b_val Rel T7 h.1 h.2.1).trans h.2.2
  have hb8 : bc 8 = 22063924 := by
    have h := check_all.2.2.2.2.2.2.2.1
    exact (b_val Rel T8 h.1 h.2.1).trans h.2.2
  have hb9 : bc 9 = 56687801 := by
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
lemma a_poly (n : ℕ) : (a n : ℚ) = 1 + (568 / 45) * (n : ℚ) + (9739 / 168) * (n : ℚ) ^ 2 + (291427 / 2268) * (n : ℚ) ^ 3 + (74183 / 480) * (n : ℚ) ^ 4 + (57133 / 540) * (n : ℚ) ^ 5 + (1991 / 48) * (n : ℚ) ^ 6 + (244 / 27) * (n : ℚ) ^ 7 + (1123 / 1120) * (n : ℚ) ^ 8 + (124 / 2835) * (n : ℚ) ^ 9 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := c_vals
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero, choose_q, prod_range_succ, prod_range_zero,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, Nat.factorial]
  push_cast
  ring

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (512 + 6115 * X + 10390 * X ^ 2 - 618 * X ^ 3 - 622 * X ^ 4 + 36 * X ^ 5 + 94 * X ^ 6 - 44 * X ^ 7 + 10 * X ^ 8 - X ^ 9) := by
  have v1 : (a 1 : ℚ) = 512 := by rw [a_poly]; norm_num
  have v2 : (a 2 : ℚ) = 11235 := by rw [a_poly]; norm_num
  have v3 : (a 3 : ℚ) = 99700 := by rw [a_poly]; norm_num
  have v4 : (a 4 : ℚ) = 552247 := by rw [a_poly]; norm_num
  have v5 : (a 5 : ℚ) = 2276028 := by rw [a_poly]; norm_num
  have v6 : (a 6 : ℚ) = 7642875 := by rw [a_poly]; norm_num
  have v7 : (a 7 : ℚ) = 22063924 := by rw [a_poly]; norm_num
  have v8 : (a 8 : ℚ) = 56687801 := by rw [a_poly]; norm_num
  have v9 : (a 9 : ℚ) = 132734964 := by rw [a_poly]; norm_num
  have v10 : (a 10 : ℚ) = 288116455 := by rw [a_poly]; norm_num
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 10 = A - C (10 : ℚ) * (A * X ^ 1) + C (45 : ℚ) * (A * X ^ 2) - C (120 : ℚ) * (A * X ^ 3) + C (210 : ℚ) * (A * X ^ 4) - C (252 : ℚ) * (A * X ^ 5) + C (210 : ℚ) * (A * X ^ 6) - C (120 : ℚ) * (A * X ^ 7) + C (45 : ℚ) * (A * X ^ 8) - C (10 : ℚ) * (A * X ^ 9) + A * X ^ 10 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (512 + 6115 * X + 10390 * X ^ 2 - 618 * X ^ 3 - 622 * X ^ 4 + 36 * X ^ 5 + 94 * X ^ 6 - 44 * X ^ 7 + 10 * X ^ 8 - X ^ 9) : ℚ⟦X⟧) = X ^ 1 * C (512 : ℚ) + X ^ 2 * C (6115 : ℚ) + X ^ 3 * C (10390 : ℚ) - X ^ 4 * C (618 : ℚ) - X ^ 5 * C (622 : ℚ) + X ^ 6 * C (36 : ℚ) + X ^ 7 * C (94 : ℚ) - X ^ 8 * C (44 : ℚ) + X ^ 9 * C (10 : ℚ) - X ^ 10 := by
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
      X * (512 + 6115 * X + 10390 * X ^ 2 - 618 * X ^ 3 - 622 * X ^ 4 + 36 * X ^ 5 + 94 * X ^ 6 - 44 * X ^ 7 + 10 * X ^ 8 - X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a200844

theorem OMA.solution : type_of% @OMA.S_oeis_a200844.main :=
  OMA.S_oeis_a200844.conjecture
