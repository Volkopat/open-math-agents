import OMAStatements.S_oeis_a200786

/-!
Proof of Barker's conjectures for A200786 (0..n arrays x(0..3) of 4 elements without any two
consecutive increases).

Group the arrays by their middle entries `(x1, x2)`. If `x2 ≤ x1`, no three consecutive entries
increase, so all `(n + 1)^2` choices of `(x0, x3)` are allowed. If `x1 < x2`, the array has no
two consecutive increases exactly when `x1 ≤ x0` and `x3 ≤ x2`, which leaves
`(n + 1 - x1) (x2 + 1)` choices. Summing over the middle pairs in `0..n` (by induction on the
side `m` of the square `0..m-1` of middle pairs, with `n` fixed) gives
`24 a(n) = 24 + 106n + 151n^2 + 86n^3 + 17n^4` for every `n`. The recurrence and the generating
function follow by comparing coefficients: the fifth difference of a polynomial of degree 4
vanishes.
-/

namespace OMA.Helpers

open OMA.S_oeis_a200786 Finset

/-- The number of completions `(x0, x3)` of a middle pair `(x1, x2)` of entries in `0..n`. -/
def g (n x1 x2 : ℕ) : ℕ := if x1 < x2 then (n + 1 - x1) * (x2 + 1) else (n + 1) ^ 2

theorem a_eq_sum (n : ℕ) : a n = ∑ x1 ∈ range (n + 1), ∑ x2 ∈ range (n + 1), g n x1 x2 := by
  unfold a
  rw [card_filter]
  simp only [sum_product]
  rw [sum_comm]
  refine sum_congr rfl (fun x1 hx1 => ?_)
  rw [sum_comm]
  refine sum_congr rfl (fun x2 hx2 => ?_)
  rw [mem_range] at hx1 hx2
  unfold g
  split_ifs with h
  · have e : ∀ x0 x3 : ℕ, (if ¬ (x0 < x1 ∧ x1 < x2) ∧ ¬ (x1 < x2 ∧ x2 < x3) then 1 else 0) =
        (if x1 ≤ x0 then 1 else 0) * (if x3 ≤ x2 then 1 else 0) := by
      intro x0 x3
      split_ifs <;> omega
    simp only [e]
    rw [← sum_mul_sum, sum_boole, sum_boole]
    have e1 : (range (n + 1)).filter (fun x0 => x1 ≤ x0) = Ico x1 (n + 1) := by
      ext x0
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    have e2 : (range (n + 1)).filter (fun x3 => x3 ≤ x2) = range (x2 + 1) := by
      ext x3
      simp only [mem_filter, mem_range]
      omega
    rw [e1, e2, Nat.card_Ico, card_range]
    simp
  · have e : ∀ x0 x3 : ℕ, (if ¬ (x0 < x1 ∧ x1 < x2) ∧ ¬ (x1 < x2 ∧ x2 < x3) then 1 else 0) = 1 := by
      intro x0 x3
      rw [if_pos]
      omega
    simp only [e, sum_const, card_range, smul_eq_mul]
    ring

/-- `g` over `ℚ`, with the bound `N` as a parameter: no truncated subtraction. -/
def gQ (N x1 x2 : ℕ) : ℚ := if x1 < x2 then ((N : ℚ) + 1 - x1) * (x2 + 1) else ((N : ℚ) + 1) ^ 2

theorem g_cast (n x1 x2 : ℕ) (h : x1 ≤ n) : (g n x1 x2 : ℚ) = gQ n x1 x2 := by
  unfold g gQ
  split_ifs
  · rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  · push_cast
    ring

theorem col_sum (N m : ℕ) :
    ∑ x1 ∈ range m, ((N : ℚ) + 1 - x1) = m * (N + 1) - m * (m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- The double sum of `gQ N` over `0..m-1`, times 24. -/
theorem S_closed (N m : ℕ) :
    24 * ∑ x1 ∈ range m, ∑ x2 ∈ range m, gQ N x1 x2 =
      12 * (N : ℚ) ^ 2 * m ^ 2 + 12 * N ^ 2 * m + 8 * N * m ^ 3 + 24 * N * m ^ 2 + 16 * N * m
        - 3 * m ^ 4 + 14 * m ^ 3 + 15 * m ^ 2 - 2 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have row : ∑ x2 ∈ range m, gQ N m x2 = m * ((N : ℚ) + 1) ^ 2 := by
      have e : ∀ x2 ∈ range m, gQ N m x2 = ((N : ℚ) + 1) ^ 2 := by
        intro x2 hx2
        rw [mem_range] at hx2
        unfold gQ
        rw [if_neg (by omega)]
      rw [sum_congr rfl e, sum_const, card_range, nsmul_eq_mul]
    have col : ∑ x1 ∈ range m, gQ N x1 m = (m * (N + 1) - m * (m - 1) / 2) * (m + 1) := by
      have e : ∀ x1 ∈ range m, gQ N x1 m = ((N : ℚ) + 1 - x1) * (m + 1) := by
        intro x1 hx1
        rw [mem_range] at hx1
        unfold gQ
        rw [if_pos hx1]
      rw [sum_congr rfl e, ← sum_mul, col_sum]
    have diag : gQ N m m = ((N : ℚ) + 1) ^ 2 := by
      unfold gQ
      rw [if_neg (lt_irrefl m)]
    rw [sum_range_succ]
    simp only [sum_range_succ, sum_add_distrib]
    rw [row, col, diag]
    push_cast
    linear_combination ih

/-- The closed form, for every `n` (also `n = 0`, where `a 0 = 1`). -/
theorem a_closed (n : ℕ) :
    24 * (a n : ℚ) = 24 + 106 * n + 151 * n ^ 2 + 86 * n ^ 3 + 17 * n ^ 4 := by
  rw [a_eq_sum]
  push_cast
  have e : ∀ x1 ∈ range (n + 1), ∑ x2 ∈ range (n + 1), (g n x1 x2 : ℚ) =
      ∑ x2 ∈ range (n + 1), gQ n x1 x2 := by
    intro x1 hx1
    rw [mem_range] at hx1
    exact sum_congr rfl (fun x2 _ => g_cast n x1 x2 (by omega))
  rw [sum_congr rfl e, S_closed]
  push_cast
  ring

theorem a_formula (n : ℕ) :
    (a n : ℚ) = (24 + 106 * n + 151 * n ^ 2 + 86 * n ^ 3 + 17 * n ^ 4) / 24 := by
  have h := a_closed n
  linarith

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  have hQ : (a n : ℚ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4)
      + a (n - 5) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
      show k + 6 - 5 = k + 1 by omega]
    rw [a_formula (k + 6), a_formula (k + 5), a_formula (k + 4), a_formula (k + 3),
      a_formula (k + 2), a_formula (k + 1)]
    push_cast
    ring
  exact_mod_cast hQ

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      (X * (16 - 5 * X + 10 * X ^ 2 - 5 * X ^ 3 + X ^ 4)) * ((1 - X) ^ 5)⁻¹ := by
  have hD : constantCoeff ((1 - X : ℚ⟦X⟧) ^ 5) ≠ 0 := by
    simp
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hD]
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have key : A * (1 - X) ^ 5 =
      A * X ^ 0 - C (5 : ℚ) * (A * X ^ 1) + C (10 : ℚ) * (A * X ^ 2) - C (10 : ℚ) * (A * X ^ 3) +
        C (5 : ℚ) * (A * X ^ 4) - A * X ^ 5 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (16 - 5 * X + 10 * X ^ 2 - 5 * X ^ 3 + X ^ 4) =
      C (16 : ℚ) * X ^ 1 - C (5 : ℚ) * X ^ 2 + C (10 : ℚ) * X ^ 3 - C (5 : ℚ) * X ^ 4 +
        C (1 : ℚ) * X ^ 5 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [a_formula]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega,
      if_true, if_false]
    rw [a_formula (j + 6), a_formula (j + 5), a_formula (j + 4), a_formula (j + 3),
      a_formula (j + 2), a_formula (j + 1)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a200786.main :=
  ⟨OMA.Helpers.gen_fun, fun n _ => OMA.Helpers.a_formula n, OMA.Helpers.recurrence⟩
