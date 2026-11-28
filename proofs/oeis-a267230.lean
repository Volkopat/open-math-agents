import OMAStatements.S_oeis_a267230

namespace OMA.S_oeis_a267230

open Finset

section Gen

variable {m : ℕ} (r : Fin m → Fin m → Prop) [DecidableRel r]

/-- The counted arrays, for an arbitrary alphabet `Fin m` and an arbitrary relation `r`
between a later element and the first repeated value. -/
def GF {n : ℕ} (x : Fin n → Fin m) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → x i = x j →
    (∀ k l : Fin n, k.val + 1 = l.val → l.val < j.val → x k ≠ x l) →
    ∀ t : Fin n, j < t → r (x t) (x j)

/-- The same condition for the first `n` values of a sequence. -/
def GN (n : ℕ) (f : ℕ → Fin m) : Prop :=
  ∀ i, i + 1 < n → f i = f (i + 1) → (∀ k, k < i → f k ≠ f (k + 1)) →
    ∀ t, i + 1 < t → t < n → r (f t) (f (i + 1))

/-- An array extended to a sequence by a default value. -/
def ext (d : Fin m) {n : ℕ} (x : Fin n → Fin m) (k : ℕ) : Fin m :=
  if h : k < n then x ⟨k, h⟩ else d

/-- Prepend `c` to a sequence. -/
def sh (c : Fin m) (f : ℕ → Fin m) : ℕ → Fin m
  | 0 => c
  | k + 1 => f k

theorem ext_lt (d : Fin m) {n : ℕ} (x : Fin n → Fin m) (k : ℕ) (h : k < n) :
    ext d x k = x ⟨k, h⟩ := dif_pos h

theorem GF_iff (d : Fin m) {n : ℕ} (x : Fin n → Fin m) : GF r x ↔ GN r n (ext d x) := by
  constructor
  · intro h i hi hrep hfirst t hit htn
    rw [ext_lt d x _ (by omega), ext_lt d x _ (by omega)] at hrep
    rw [ext_lt d x _ htn, ext_lt d x _ hi]
    refine h ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl hrep ?_ ⟨t, htn⟩ (Fin.mk_lt_mk.mpr hit)
    rintro ⟨k, hk⟩ ⟨l, hl⟩ hkl hlj
    simp only at hkl hlj
    subst hkl
    have := hfirst k (by omega)
    rwa [ext_lt d x _ hk, ext_lt d x _ hl] at this
  · rintro h ⟨i, hi⟩ ⟨j, hj⟩ hij hrep hfirst ⟨t, ht⟩ hjt
    simp only at hij
    subst hij
    have hjt' : i + 1 < t := hjt
    have := h i hj (by rwa [ext_lt d x _ hi, ext_lt d x _ hj]) (fun k hk => by
      rw [ext_lt d x _ (by omega), ext_lt d x _ (by omega)]
      exact hfirst ⟨k, by omega⟩ ⟨k + 1, by omega⟩ rfl (by simp only; omega)) t hjt' ht
    rwa [ext_lt d x _ ht, ext_lt d x _ hj] at this

theorem GN_sh (c : Fin m) (f : ℕ → Fin m) (n : ℕ) :
    GN r (n + 2) (sh c f) ↔ if c = f 0 then (∀ t, t < n → r (f (t + 1)) c) else GN r (n + 1) f := by
  by_cases hc : c = f 0
  · rw [if_pos hc]
    constructor
    · intro h t ht
      have := h 0 (by omega) hc (fun k hk => absurd hk (Nat.not_lt_zero _)) (t + 2) (by omega)
        (by omega)
      rw [hc]
      exact this
    · intro h i hi hrep hfirst t hit htn
      rcases i with _ | i
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
        show r (f (t' + 1)) (f 0)
        rw [← hc]
        exact h t' (by omega)
      · exact absurd hc (hfirst 0 (by omega))
  · rw [if_neg hc]
    constructor
    · intro h i hi hrep hfirst t hit htn
      exact h (i + 1) (by omega) hrep (fun k hk => by
        rcases k with _ | k
        · exact hc
        · exact hfirst k (by omega)) (t + 1) (by omega) (by omega)
    · intro h i hi hrep hfirst t hit htn
      rcases i with _ | i
      · exact absurd hrep hc
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        exact h i (by omega) hrep (fun k hk => hfirst (k + 1) (by omega)) t' (by omega) (by omega)

theorem sum_cons {β : Type*} [AddCommMonoid β] {n : ℕ} (F : (Fin (n + 1) → Fin m) → β) :
    ∑ x, F x = ∑ c, ∑ y : Fin n → Fin m, F (Fin.cons c y) := by
  rw [← (Fin.consEquiv fun _ => Fin m).sum_comp, Fintype.sum_prod_type]
  rfl

theorem ext_cons (d : Fin m) {n : ℕ} (c : Fin m) (y : Fin n → Fin m) :
    ext d (Fin.cons c y : Fin (n + 1) → Fin m) = sh c (ext d y) := by
  funext k
  rcases k with _ | k
  · rw [ext_lt d _ 0 (by omega)]
    rfl
  · by_cases hk : k < n
    · rw [ext_lt d _ (k + 1) (by omega)]
      show _ = ext d y k
      rw [ext_lt d y k hk]
      exact Fin.cons_succ (α := fun _ => Fin m) c y ⟨k, hk⟩
    · show ext d _ (k + 1) = ext d y k
      unfold ext
      rw [dif_neg (by omega), dif_neg hk]

open Classical in
/-- Number of tails `y` of length `n` such that `c` followed by `y` is counted. -/
noncomputable def T (d : Fin m) (n : ℕ) (c : Fin m) : ℕ :=
  ∑ y : Fin n → Fin m, if GN r (n + 1) (sh c (ext d y)) then 1 else 0

open Classical in
/-- Number of letters allowed after the first repeated value `c`. -/
noncomputable def K (c : Fin m) : ℕ := ∑ e : Fin m, if r e c then 1 else 0

open Classical in
theorem count_succ (d : Fin m) (n : ℕ) :
    (∑ x : Fin (n + 1) → Fin m, if GF r x then 1 else 0) = ∑ c, T r d n c := by
  rw [sum_cons]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← ext_cons]
  exact if_congr (GF_iff r d _) rfl rfl

open Classical in
theorem T_zero (d : Fin m) (c : Fin m) : T r d 0 c = 1 := by
  unfold T
  rw [Fintype.sum_unique, if_pos]
  intro i hi
  omega

open Classical in
theorem T_succ (d : Fin m) (n : ℕ) (c : Fin m) :
    T r d (n + 1) c = ∑ e, if c = e then K r c ^ n else T r d n e := by
  unfold T
  rw [sum_cons]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hce : c = e
  · rw [if_pos hce]
    have h1 : ∀ y : Fin n → Fin m,
        (if GN r (n + 1 + 1) (sh c (ext d (Fin.cons e y : Fin (n + 1) → Fin m))) then 1 else 0) =
          ∏ i, (if r (y i) c then 1 else 0) := by
      intro y
      have key : GN r (n + 1 + 1) (sh c (ext d (Fin.cons e y : Fin (n + 1) → Fin m))) ↔
          ∀ i, r (y i) c := by
        rw [ext_cons, GN_sh]
        have h0 : c = sh e (ext d y) 0 := hce
        rw [if_pos h0]
        refine ⟨fun h i => ?_, fun h t ht => ?_⟩
        · have := h i.val i.isLt
          rwa [show sh e (ext d y) (i.val + 1) = ext d y i.val from rfl,
            ext_lt d y _ i.isLt] at this
        · rw [show sh e (ext d y) (t + 1) = ext d y t from rfl, ext_lt d y _ ht]
          exact h _
      by_cases hk : GN r (n + 1 + 1) (sh c (ext d (Fin.cons e y : Fin (n + 1) → Fin m)))
      · rw [if_pos hk]
        exact (Finset.prod_eq_one fun i _ => if_pos (key.mp hk i)).symm
      · rw [if_neg hk]
        obtain ⟨i, hi⟩ := not_forall.mp (fun h => hk (key.mpr h))
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm
    rw [Finset.sum_congr rfl fun y _ => h1 y]
    unfold K
    rw [Fintype.sum_pow]
  · rw [if_neg hce]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ext_cons]
    have key := GN_sh r c (sh e (ext d y)) n
    have h0 : ¬ c = sh e (ext d y) 0 := hce
    rw [if_neg h0] at key
    exact if_congr key rfl rfl

theorem sum_ite_eq_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι) (A : ℤ) (B : ι → ℤ) :
    (∑ e, if c = e then A else B e) = A + ∑ e, B e - B c := by
  have : ∀ e, (if c = e then A else B e) = (if c = e then A - B e else 0) + B e := by
    intro e
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun e _ => this e, Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  ring

open Classical in
/-- The scalar recursion: with `S n = ∑ c, T n c`, `S (n+1) = (m-1) S n + ∑ c, K c ^ n`. -/
theorem S_succ (d : Fin m) (n : ℕ) :
    (∑ c, (T r d (n + 1) c : ℤ)) = (m - 1) * (∑ c, (T r d n c : ℤ)) + ∑ c, (K r c : ℤ) ^ n := by
  have : ∀ c, (T r d (n + 1) c : ℤ) = (K r c : ℤ) ^ n + ∑ e, (T r d n e : ℤ) - T r d n c := by
    intro c
    rw [T_succ, ← sum_ite_eq_aux]
    push_cast
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Gen

open Classical in
/-- The statement's count as a sum. -/
theorem a_eq (n : ℕ) :
    a n = ∑ x : Fin n → Fin 7, if GF (fun u v => u < v) x then 1 else 0 := by
  unfold a
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun x _ => if_congr Iff.rfl rfl rfl

theorem K_val (c : Fin 7) : K (fun u v : Fin 7 => u < v) c = c.val := by
  fin_cases c <;> decide

theorem rec1 : (a 1 : ℤ) = 7 := by
  rw [a_eq, count_succ _ 0]
  simp [T_zero]

theorem rec2 (n : ℕ) :
    (a (n + 2) : ℤ) = 6 * a (n + 1) + (0 ^ n + 1 + 2 ^ n + 3 ^ n + 4 ^ n + 5 ^ n + 6 ^ n) := by
  rw [a_eq, a_eq, count_succ _ 0, count_succ _ 0]
  push_cast
  rw [S_succ]
  simp [Fin.sum_univ_seven, K_val]
  try ring

theorem closed (k : ℕ) :
    360 * (a (k + 2) : ℤ) = -45 * 2 ^ (k + 2) - 40 * 3 ^ (k + 2) - 45 * 4 ^ (k + 2) -
      72 * 5 ^ (k + 2) + 557 * 6 ^ (k + 2) + 10 * 6 ^ (k + 2) * (k + 2) - 72 := by
  induction k with
  | zero => rw [rec2, rec1]; norm_num
  | succ k ih =>
    rw [rec2, show k + 1 + 1 = k + 2 by ring, zero_pow (by omega)]
    push_cast
    linear_combination 6 * ih

theorem closedQ (n : ℕ) (hn : 1 < n) :
    (a n : ℚ) = (-45 * 2 ^ n - 40 * 3 ^ n - 45 * 4 ^ n - 72 * 5 ^ n + 557 * 6 ^ n +
        5 * 2 ^ (1 + n) * 3 ^ n * n - 72) / 360 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h := closed k
  have h' : 360 * (a (k + 2) : ℚ) = -45 * 2 ^ (k + 2) - 40 * 3 ^ (k + 2) - 45 * 4 ^ (k + 2) -
      72 * 5 ^ (k + 2) + 557 * 6 ^ (k + 2) + 10 * 6 ^ (k + 2) * (k + 2) - 72 := by
    exact_mod_cast h
  have h6 : (6 : ℚ) ^ (k + 2) = 2 ^ (k + 2) * 3 ^ (k + 2) := by
    rw [← mul_pow]
    norm_num
  push_cast
  linear_combination h' / 360 + (10 * ((k : ℚ) + 2) / 360) * h6

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X) * (1 - 5 * X) * (1 - 6 * X) ^ 2) =
      X * (7 - 140 * X + 1099 * X ^ 2 - 4270 * X ^ 3 + 8428 * X ^ 4 - 7476 * X ^ 5 +
        1512 * X ^ 6 + 720 * X ^ 7) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X) * (1 - 5 * X) * (1 - 6 * X) ^ 2) =
      A - C 27 * (A * X ^ 1) + C 301 * (A * X ^ 2) - C 1785 * (A * X ^ 3) + C 6034 * (A * X ^ 4) - C 11508 * (A * X ^ 5) + C 11304 * (A * X ^ 6) - C 4320 * (A * X ^ 7) := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (7 - 140 * X + 1099 * X ^ 2 - 4270 * X ^ 3 + 8428 * X ^ 4 - 7476 * X ^ 5 +
        1512 * X ^ 6 + 720 * X ^ 7) : ℚ⟦X⟧) =
      C 7 * X ^ 1 - C 140 * X ^ 2 + C 1099 * X ^ 3 - C 4270 * X ^ 4 + C 8428 * X ^ 5 - C 7476 * X ^ 6 + C 1512 * X ^ 7 + C 720 * X ^ 8 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, ∀ k, b k = (a k : ℚ) := ⟨fun k => (a k : ℚ), fun _ => rfl⟩
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℚ) else b k := fun k => by rw [hA, coeff_mk, hb]
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_C, hc]
  have v1 : b 1 = 7 := by rw [hb]; exact_mod_cast rec1
  have v2 : b 2 = 49 := by rw [hb, closedQ 2 (by norm_num)]; norm_num
  have v3 : b 3 = 315 := by rw [hb, closedQ 3 (by norm_num)]; norm_num
  have v4 : b 4 = 1981 := by rw [hb, closedQ 4 (by norm_num)]; norm_num
  have v5 : b 5 = 12327 := by rw [hb, closedQ 5 (by norm_num)]; norm_num
  have v6 : b 6 = 76237 := by rw [hb, closedQ 6 (by norm_num)]; norm_num
  have v7 : b 7 = 469623 := by rw [hb, closedQ 7 (by norm_num)]; norm_num
  have v8 : b 8 = 2884909 := by rw [hb, closedQ 8 (by norm_num)]; norm_num
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 9 := ⟨n - 9, by omega⟩
    simp only [show j + 9 - 1 = j + 8 by omega,
      show j + 9 - 2 = j + 7 by omega,
      show j + 9 - 3 = j + 6 by omega,
      show j + 9 - 4 = j + 5 by omega,
      show j + 9 - 5 = j + 4 by omega,
      show j + 9 - 6 = j + 3 by omega,
      show j + 9 - 7 = j + 2 by omega,
      show j + 9 - 8 = j + 1 by omega,
      show 1 ≤ j + 9 by omega,
      show 2 ≤ j + 9 by omega,
      show 3 ≤ j + 9 by omega,
      show 4 ≤ j + 9 by omega,
      show 5 ≤ j + 9 by omega,
      show 6 ≤ j + 9 by omega,
      show 7 ≤ j + 9 by omega,
      show 8 ≤ j + 9 by omega,
      show ¬ j + 9 = 0 by omega,
      show ¬ j + 8 = 0 by omega,
      show ¬ j + 7 = 0 by omega,
      show ¬ j + 6 = 0 by omega,
      show ¬ j + 5 = 0 by omega,
      show ¬ j + 4 = 0 by omega,
      show ¬ j + 3 = 0 by omega,
      show ¬ j + 2 = 0 by omega,
      show ¬ j + 1 = 0 by omega,
      if_true, if_false, hb]
    rw [closedQ (j + 9) (by omega), closedQ (j + 8) (by omega), closedQ (j + 7) (by omega), closedQ (j + 6) (by omega), closedQ (j + 5) (by omega), closedQ (j + 4) (by omega), closedQ (j + 3) (by omega), closedQ (j + 2) (by omega)]
    push_cast
    ring

theorem conjecture : type_of% @main := ⟨gf, closedQ⟩

end OMA.S_oeis_a267230

theorem OMA.solution : type_of% @OMA.S_oeis_a267230.main :=
  OMA.S_oeis_a267230.conjecture
