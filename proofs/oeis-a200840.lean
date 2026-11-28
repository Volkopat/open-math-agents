import OMAStatements.S_oeis_a200840

/-!
Proof of Barker's conjectures for A200840 (arrays x(0..4) with entries in 0..n without two
consecutive increases or two consecutive decreases).

Write `Ok3 a b c` for "neither `a < b < c` nor `a > b > c`". An array `(s, u, v, w, t)` is good
iff `Ok3 s u v`, `Ok3 u v w` and `Ok3 v w t` (`good_iff`), so `a n` is a five-fold sum of products
of indicators, which we order with the middle entry `v` outermost (`a_eq`). For fixed `u, v` the
number of `s ∈ 0..n` with `Ok3 s u v` is `g n u v`, equal to `n + 1 - u`, `n + 1` or `u + 1`
according as `u < v`, `u = v` or `u > v` (`g_lt`, `g_eq`, `g_gt`); by reversal (`Ok3_symm`) the
number of `t` with `Ok3 v w t` is `g n w v`. So the arrays with middle entry `v` number
`Sum_u g n u v * W n u v`, where `W n u v` sums `g n w v` over the `w` with `Ok3 u v w`: all
`w ≤ v` if `u < v`, all `w` if `u = v`, all `w ≥ v` if `u > v` (`W_lt`, `W_eq`, `W_gt`). Splitting
every sum over `0..n` at `v` (`split3`) and summing the arithmetic progressions gives the closed
form `Q n v` (`inner_closed`), a polynomial in `n` and `v`; summing it over `v ≤ n` (`sum_Q`)
gives, for every `n`,
  a(n) = (4/15) n^5 + (17/6) n^4 + (28/3) n^3 + (73/6) n^2 + (32/5) n + 1   (`closedQ`).
The recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a200840 Finset

/-- No two consecutive increases and no two consecutive decreases at `a, b, c`. -/
def Ok3 (a b c : ℕ) : Prop := ¬ (a < b ∧ b < c) ∧ ¬ (a > b ∧ b > c)

instance decOk3 (a b c : ℕ) : Decidable (Ok3 a b c) := by
  unfold Ok3
  infer_instance

instance decGood {n : ℕ} (x : Fin 5 → Fin (n + 1)) : Decidable (Good x) := by
  unfold Good
  infer_instance

theorem Ok3_symm (a b c : ℕ) : Ok3 a b c ↔ Ok3 c b a := by
  unfold Ok3
  omega

theorem good_iff {n : ℕ} (x : Fin 5 → Fin (n + 1)) :
    Good x ↔ Ok3 (x 0) (x 1) (x 2) ∧ Ok3 (x 1) (x 2) (x 3) ∧ Ok3 (x 2) (x 3) (x 4) := by
  unfold Good Ok3
  simp only [Fin.lt_def, gt_iff_lt]
  constructor
  · intro h
    exact ⟨h 0 1 2 rfl rfl, h 1 2 3 rfl rfl, h 2 3 4 rfl rfl⟩
  · rintro ⟨h1, h2, h3⟩ ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk
    simp only at hij hjk
    subst hij hjk
    have hi3 : i < 3 := by omega
    interval_cases i
    · exact h1
    · exact h2
    · exact h3

/-- The array with entries `s, u, v, w, t`, listed with the middle entry first. -/
def tup (n : ℕ) : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1) ≃
    (Fin 5 → Fin (n + 1)) where
  toFun p := ![p.2.2.2.1, p.2.1, p.1, p.2.2.1, p.2.2.2.2]
  invFun x := (x 2, x 1, x 3, x 0, x 4)
  left_inv p := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

theorem ite3 (A B D : Prop) [Decidable A] [Decidable B] [Decidable D] :
    (if A ∧ B ∧ D then (1 : ℚ) else 0) =
      (if A then 1 else 0) * (if B then 1 else 0) * (if D then 1 else 0) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hD : D <;> simp [hA, hB, hD]

theorem a_eq (n : ℕ) : (a n : ℚ) =
    ∑ v ∈ range (n + 1), ∑ u ∈ range (n + 1), ∑ w ∈ range (n + 1), ∑ s ∈ range (n + 1),
      ∑ t ∈ range (n + 1),
        (if Ok3 s u v then (1 : ℚ) else 0) * (if Ok3 u v w then 1 else 0) *
          (if Ok3 v w t then 1 else 0) := by
  have h1 : (a n : ℚ) = ∑ x : Fin 5 → Fin (n + 1), if Good x then (1 : ℚ) else 0 := by
    unfold a
    rw [Fintype.card_subtype, Finset.natCast_card_filter]
  rw [h1, ← (tup n).sum_comp]
  simp only [Fintype.sum_prod_type, Finset.sum_range]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ =>
    Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun t _ => ?_
  rw [← ite3]
  refine if_congr ?_ rfl rfl
  rw [good_iff]
  rfl

/-- Splitting a sum over `0..v+k` into the parts below `v`, at `v`, and above `v`. -/
theorem split3 (f : ℕ → ℚ) (v k : ℕ) :
    ∑ u ∈ range (v + k + 1), f u = ∑ u ∈ range v, f u + f v + ∑ j ∈ range k, f (v + 1 + j) := by
  rw [show v + k + 1 = v + 1 + k by ring, Finset.sum_range_add, Finset.sum_range_succ]

theorem sum_sub (c : ℚ) (m : ℕ) : ∑ i ∈ range m, (c - i) = m * c - m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_add (c : ℚ) (m : ℕ) : ∑ i ∈ range m, (c + i) = m * c + m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `g n u v`: the number of `s ∈ 0..n` with `Ok3 s u v`. -/
def g (n u v : ℕ) : ℚ := ∑ s ∈ range (n + 1), if Ok3 s u v then 1 else 0

theorem g_lt {n u v : ℕ} (huv : u < v) (hv : v ≤ n) : g n u v = n + 1 - u := by
  obtain ⟨k, rfl⟩ : ∃ k, n = u + k := ⟨n - u, by omega⟩
  unfold g
  rw [split3]
  have h1 : ∑ s ∈ range u, (if Ok3 s u v then (1 : ℚ) else 0) = 0 :=
    Finset.sum_eq_zero fun s hs => if_neg (by have := mem_range.1 hs; unfold Ok3; omega)
  have h3 : ∑ j ∈ range k, (if Ok3 (u + 1 + j) u v then (1 : ℚ) else 0) = k := by
    rw [Finset.sum_congr rfl fun j _ => if_pos (by unfold Ok3; omega)]
    simp
  rw [h1, h3, if_pos (by unfold Ok3; omega)]
  push_cast
  ring

theorem g_eq (n v : ℕ) : g n v v = n + 1 := by
  unfold g
  rw [Finset.sum_congr rfl fun s _ => if_pos (by unfold Ok3; omega)]
  simp

theorem g_gt {n u v : ℕ} (hvu : v < u) (hu : u ≤ n) : g n u v = u + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = u + k := ⟨n - u, by omega⟩
  unfold g
  rw [split3]
  have h1 : ∑ s ∈ range u, (if Ok3 s u v then (1 : ℚ) else 0) = u := by
    rw [Finset.sum_congr rfl fun s hs =>
      if_pos (by have := mem_range.1 hs; unfold Ok3; omega)]
    simp
  have h3 : ∑ j ∈ range k, (if Ok3 (u + 1 + j) u v then (1 : ℚ) else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => if_neg (by unfold Ok3; omega)
  rw [h1, h3, if_pos (by unfold Ok3; omega)]
  ring

/-- `Slt n v`: the sum of `g n w v` over `w < v`. -/
def Slt (n v : ℕ) : ℚ := (v : ℚ) * ((n : ℚ) + 1) - (v : ℚ) * ((v : ℚ) - 1) / 2

/-- `Sgt n v`: the sum of `g n w v` over `v < w ≤ n`. -/
def Sgt (n v : ℕ) : ℚ :=
  ((n : ℚ) - v) * ((v : ℚ) + 2) + ((n : ℚ) - v) * ((n : ℚ) - v - 1) / 2

theorem lo_sum {n v : ℕ} (hv : v ≤ n) : ∑ w ∈ range v, g n w v = Slt n v := by
  rw [Finset.sum_congr rfl fun w hw => g_lt (mem_range.1 hw) hv]
  rw [sum_sub]
  unfold Slt
  ring

theorem hi_sum (v k : ℕ) : ∑ j ∈ range k, g (v + k) (v + 1 + j) v = Sgt (v + k) v := by
  rw [Finset.sum_congr rfl fun j hj => g_gt (by omega) (by have := mem_range.1 hj; omega)]
  have e : ∀ j : ℕ, (((v + 1 + j : ℕ) : ℚ) + 1) = ((v : ℚ) + 2) + j := fun j => by
    push_cast
    ring
  simp only [e]
  rw [sum_add]
  unfold Sgt
  push_cast
  ring

/-- `W n u v`: the sum of `g n w v` over the `w ∈ 0..n` with `Ok3 u v w`. -/
def W (n u v : ℕ) : ℚ := ∑ w ∈ range (n + 1), (if Ok3 u v w then 1 else 0) * g n w v

theorem W_lt {n u v : ℕ} (huv : u < v) (hv : v ≤ n) : W n u v = Slt n v + ((n : ℚ) + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = v + k := ⟨n - v, by omega⟩
  unfold W
  rw [split3]
  have h1 : ∑ w ∈ range v, (if Ok3 u v w then (1 : ℚ) else 0) * g (v + k) w v =
      ∑ w ∈ range v, g (v + k) w v :=
    Finset.sum_congr rfl fun w hw => by
      rw [if_pos (by have := mem_range.1 hw; unfold Ok3; omega), one_mul]
  have h3 : ∑ j ∈ range k,
      (if Ok3 u v (v + 1 + j) then (1 : ℚ) else 0) * g (v + k) (v + 1 + j) v = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [if_neg (by unfold Ok3; omega), zero_mul]
  rw [h1, h3, lo_sum (by omega), if_pos (by unfold Ok3; omega), one_mul, g_eq]
  ring

theorem W_eq {n v : ℕ} (hv : v ≤ n) : W n v v = Slt n v + ((n : ℚ) + 1) + Sgt n v := by
  obtain ⟨k, rfl⟩ : ∃ k, n = v + k := ⟨n - v, by omega⟩
  unfold W
  rw [split3]
  have h1 : ∑ w ∈ range v, (if Ok3 v v w then (1 : ℚ) else 0) * g (v + k) w v =
      ∑ w ∈ range v, g (v + k) w v :=
    Finset.sum_congr rfl fun w _ => by rw [if_pos (by unfold Ok3; omega), one_mul]
  have h3 : ∑ j ∈ range k,
      (if Ok3 v v (v + 1 + j) then (1 : ℚ) else 0) * g (v + k) (v + 1 + j) v =
        ∑ j ∈ range k, g (v + k) (v + 1 + j) v :=
    Finset.sum_congr rfl fun j _ => by rw [if_pos (by unfold Ok3; omega), one_mul]
  rw [h1, h3, lo_sum (by omega), hi_sum, if_pos (by unfold Ok3; omega), one_mul, g_eq]

theorem W_gt {n u v : ℕ} (hvu : v < u) (hv : v ≤ n) : W n u v = ((n : ℚ) + 1) + Sgt n v := by
  obtain ⟨k, rfl⟩ : ∃ k, n = v + k := ⟨n - v, by omega⟩
  unfold W
  rw [split3]
  have h1 : ∑ w ∈ range v, (if Ok3 u v w then (1 : ℚ) else 0) * g (v + k) w v = 0 :=
    Finset.sum_eq_zero fun w hw => by
      rw [if_neg (by have := mem_range.1 hw; unfold Ok3; omega), zero_mul]
  have h3 : ∑ j ∈ range k,
      (if Ok3 u v (v + 1 + j) then (1 : ℚ) else 0) * g (v + k) (v + 1 + j) v =
        ∑ j ∈ range k, g (v + k) (v + 1 + j) v :=
    Finset.sum_congr rfl fun j _ => by rw [if_pos (by unfold Ok3; omega), one_mul]
  rw [h1, h3, hi_sum, if_pos (by unfold Ok3; omega), one_mul, g_eq]
  ring

/-- The number of good arrays with middle entry `v`, in closed form. -/
def Q (n v : ℕ) : ℚ :=
  Slt n v * (Slt n v + ((n : ℚ) + 1)) + ((n : ℚ) + 1) * (Slt n v + ((n : ℚ) + 1) + Sgt n v) +
    Sgt n v * (((n : ℚ) + 1) + Sgt n v)

theorem inner_closed {n v : ℕ} (hv : v ≤ n) :
    ∑ u ∈ range (n + 1), g n u v * W n u v = Q n v := by
  obtain ⟨k, rfl⟩ : ∃ k, n = v + k := ⟨n - v, by omega⟩
  rw [split3]
  have h1 : ∑ u ∈ range v, g (v + k) u v * W (v + k) u v =
      ∑ u ∈ range v, g (v + k) u v * (Slt (v + k) v + (((v + k : ℕ) : ℚ) + 1)) :=
    Finset.sum_congr rfl fun u hu => by rw [W_lt (mem_range.1 hu) (by omega)]
  have h3 : ∑ j ∈ range k, g (v + k) (v + 1 + j) v * W (v + k) (v + 1 + j) v =
      ∑ j ∈ range k, g (v + k) (v + 1 + j) v * ((((v + k : ℕ) : ℚ) + 1) + Sgt (v + k) v) :=
    Finset.sum_congr rfl fun j _ => by rw [W_gt (by omega) (by omega)]
  rw [h1, h3, ← Finset.sum_mul, ← Finset.sum_mul, lo_sum (by omega), hi_sum, g_eq,
    W_eq (by omega)]
  unfold Q
  ring

theorem inner_eq (n v : ℕ) :
    ∑ u ∈ range (n + 1), ∑ w ∈ range (n + 1), ∑ s ∈ range (n + 1), ∑ t ∈ range (n + 1),
      (if Ok3 s u v then (1 : ℚ) else 0) * (if Ok3 u v w then 1 else 0) *
        (if Ok3 v w t then 1 else 0) =
    ∑ u ∈ range (n + 1), g n u v * W n u v := by
  refine Finset.sum_congr rfl fun u _ => ?_
  unfold W
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have ht : ∑ t ∈ range (n + 1), (if Ok3 v w t then (1 : ℚ) else 0) = g n w v := by
    unfold g
    exact Finset.sum_congr rfl fun t _ => if_congr (Ok3_symm v w t) rfl rfl
  rw [Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm, ht, ← Finset.sum_mul,
    ← Finset.sum_mul]
  unfold g
  ring

/-- The partial sums of `Q n v` over `v < m`. -/
def PSum (n m : ℕ) : ℚ :=
  (m : ℚ) ^ 5 / 10 - (m : ℚ) ^ 4 * n / 4 - (m : ℚ) ^ 4 / 4 + (m : ℚ) ^ 3 * (n : ℚ) ^ 2 / 6 +
    (m : ℚ) ^ 3 * n / 3 + (m : ℚ) ^ 3 - 5 * (m : ℚ) ^ 2 * n / 4 - 5 * (m : ℚ) ^ 2 / 4 +
    (m : ℚ) * (n : ℚ) ^ 4 / 4 + 5 * (m : ℚ) * (n : ℚ) ^ 3 / 2 + 85 * (m : ℚ) * (n : ℚ) ^ 2 / 12 +
    37 * (m : ℚ) * n / 6 + 7 * (m : ℚ) / 5

theorem sum_Q (n m : ℕ) : ∑ v ∈ range m, Q n v = PSum n m := by
  induction m with
  | zero => simp [PSum]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold Q Slt Sgt PSum
    push_cast
    ring

theorem closedQ (n : ℕ) : (a n : ℚ) =
    4 / 15 * (n : ℚ) ^ 5 + 17 / 6 * (n : ℚ) ^ 4 + 28 / 3 * (n : ℚ) ^ 3 + 73 / 6 * (n : ℚ) ^ 2 +
      32 / 5 * n + 1 := by
  rw [a_eq, Finset.sum_congr rfl fun v hv =>
    (inner_eq n v).trans (inner_closed (by have := mem_range.1 hv; omega)), sum_Q]
  unfold PSum
  push_cast
  ring

theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
    show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega]
  have h : ((a (m + 7) : ℤ) : ℚ) =
      ((6 * a (m + 6) - 15 * a (m + 5) + 20 * a (m + 4) - 15 * a (m + 3) + 6 * a (m + 2) -
        a (m + 1) : ℤ) : ℚ) := by
    push_cast
    simp only [closedQ]
    push_cast
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (32 - X + 10 * X ^ 2 - 14 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - X) ^ 6 =
      C 1 * (PowerSeries.mk F * X ^ 0) - C 6 * (PowerSeries.mk F * X ^ 1) +
        C 15 * (PowerSeries.mk F * X ^ 2) - C 20 * (PowerSeries.mk F * X ^ 3) +
        C 15 * (PowerSeries.mk F * X ^ 4) - C 6 * (PowerSeries.mk F * X ^ 5) +
        C 1 * (PowerSeries.mk F * X ^ 6) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (32 - X + 10 * X ^ 2 - 14 * X ^ 3 + 6 * X ^ 4 - X ^ 5) =
      C 32 * X ^ 1 - C 1 * X ^ 2 + C 10 * X ^ 3 - C 14 * X ^ 4 + C 6 * X ^ 5 -
        C 1 * X ^ 6 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 7
  · interval_cases k <;> norm_num [hF, closedQ]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    simp only [show 0 ≤ j + 7 by omega, show 1 ≤ j + 7 by omega, show 2 ≤ j + 7 by omega,
      show 3 ≤ j + 7 by omega, show 4 ≤ j + 7 by omega, show 5 ≤ j + 7 by omega,
      show 6 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega, show j + 7 - 1 = j + 6 by omega,
      show j + 7 - 2 = j + 5 by omega, show j + 7 - 3 = j + 4 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega,
      show ¬ (j + 7 = 1) by omega, show ¬ (j + 7 = 2) by omega, show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega, show ¬ (j + 7 = 5) by omega, show ¬ (j + 7 = 6) by omega,
      show ¬ (j + 7 = 0) by omega, show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 1 = 0) by omega, if_true, if_false, hF]
    rw [closedQ (j + 7), closedQ (j + 6), closedQ (j + 5), closedQ (j + 4), closedQ (j + 3),
      closedQ (j + 2), closedQ (j + 1)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a200840.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
