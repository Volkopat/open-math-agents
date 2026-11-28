import OMAStatements.S_oeis_a301653
import Mathlib

/-!
Let `S(n) = Sum_k T(n-k, k)` (in `ℕ`). The triangle satisfies the uniform rule
`T(m+1, j+1) = T(m, j+1) + T(m, j) + [j = m]` (Pascal's rule inside, the extra `1` on the
right edge, zeros beyond). Summing it along an antidiagonal gives
`S(n+2) = S(n+1) + S(n) + 1 + c(n)`, where `c(n) = #{j <= n : j = n - j}` has period 2.
Hence `S(n+4) = S(n+3) + 2 S(n+2) - S(n+1) - S(n)`, which with `S(0..3) = 0, 1, 3, 5`
says `(Sum_n S(n) x^n) * (1-x)(1+x)(1-x-x^2) = x(1+2x)`. The denominator is invertible in
`ℚ[[x]]`, so the two series agree.
-/

namespace R301653
open OMA.S_oeis_a301653 PowerSeries

theorem T_zero_of_lt (m k : ℕ) (h : m < k) : T m k = 0 := by
  rcases k with _ | k
  · omega
  rcases m with _ | m
  · rfl
  show (if k + 1 < m + 1 then T m (k + 1) + T m k else if k + 1 = m + 1 then m + 1 else 0) = 0
  rw [if_neg (show ¬ (k + 1 < m + 1) by omega), if_neg (show ¬ (k + 1 = m + 1) by omega)]

theorem T_self (m : ℕ) : T m m = m := by
  rcases m with _ | m
  · rfl
  show (if m + 1 < m + 1 then T m (m + 1) + T m m else if m + 1 = m + 1 then m + 1 else 0) = m + 1
  rw [if_neg (lt_irrefl _), if_pos rfl]

theorem T_rule (m j : ℕ) : T (m + 1) (j + 1) = T m (j + 1) + T m j + if j = m then 1 else 0 := by
  show (if j + 1 < m + 1 then T m (j + 1) + T m j else if j + 1 = m + 1 then m + 1 else 0) = _
  rcases lt_trichotomy j m with h | h | h
  · rw [if_pos (show j + 1 < m + 1 by omega), if_neg (show ¬ (j = m) by omega)]
    all_goals omega
  · subst h
    rw [if_neg (lt_irrefl _), if_pos rfl, if_pos rfl, T_zero_of_lt j (j + 1) (by omega), T_self]
    ring
  · rw [if_neg (show ¬ (j + 1 < m + 1) by omega), if_neg (show ¬ (j + 1 = m + 1) by omega),
      if_neg (show ¬ (j = m) by omega), T_zero_of_lt m (j + 1) (by omega),
      T_zero_of_lt m j (by omega)]

/-- The antidiagonal sums. -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T (n - k) k

/-- The antidiagonal sums shifted one step to the right. -/
def R (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), T (n - j) (j + 1)

/-- The number of `j <= n` with `j = n - j`. -/
def c (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), if j = n - j then 1 else 0

theorem S_succ (n : ℕ) : S (n + 1) = (n + 1) + R n := by
  unfold S R
  rw [Finset.sum_range_succ' (n := n + 1)]
  simp only [Nat.add_sub_add_right, Nat.sub_zero]
  rw [show T (n + 1) 0 = n + 1 from rfl]
  ring

theorem R_succ (n : ℕ) : R (n + 1) = R n + S n + c n := by
  unfold R S c
  rw [Finset.sum_range_succ (n := n + 1), Nat.sub_self, show T 0 (n + 1 + 1) = 0 from rfl,
    Nat.add_zero, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show n + 1 - j = n - j + 1 by omega, T_rule]

theorem c_add_two (n : ℕ) : c (n + 1 + 1) = c n := by
  unfold c
  rw [Finset.sum_range_succ' (n := n + 1 + 1), Finset.sum_range_succ (n := n + 1)]
  have b1 : (if n + 1 + 1 = n + 1 + 1 - (n + 1 + 1) then 1 else 0 : ℕ) = 0 := if_neg (by omega)
  have b0 : (if (0 : ℕ) = n + 1 + 1 - 0 then 1 else 0 : ℕ) = 0 := if_neg (by omega)
  simp only [b1, b0, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have e : (i + 1 = n + 1 + 1 - (i + 1)) = (i = n - i) :=
    propext ⟨fun h => by omega, fun h => by omega⟩
  simp only [e]

theorem S_rec (n : ℕ) : S (n + 4) + S (n + 1) + S n = S (n + 3) + 2 * S (n + 2) := by
  have h1 : S (n + 4) = (n + 3) + 1 + R (n + 3) := S_succ (n + 3)
  have h2 : S (n + 3) = (n + 2) + 1 + R (n + 2) := S_succ (n + 2)
  have h3 : S (n + 2) = (n + 1) + 1 + R (n + 1) := S_succ (n + 1)
  have h4 : S (n + 1) = n + 1 + R n := S_succ n
  have r1 : R (n + 3) = R (n + 2) + S (n + 2) + c (n + 2) := R_succ (n + 2)
  have r2 : R (n + 1) = R n + S n + c n := R_succ n
  have cc : c (n + 2) = c n := c_add_two n
  omega

theorem S0 : S 0 = 0 := by decide
theorem S1 : S 1 = 1 := by decide
theorem S2 : S 2 = 3 := by decide
theorem S3 : S 3 = 5 := by decide

theorem series_id : (mk fun n => (S n : ℚ)) * ((1 - X) * (1 + X) * (1 - X - X ^ 2)) =
    (X * (1 + 2 * X) : ℚ⟦X⟧) := by
  have hD : ((1 - X) * (1 + X) * (1 - X - X ^ 2) : ℚ⟦X⟧) =
      1 - X ^ 1 - C 2 * X ^ 2 + X ^ 3 + X ^ 4 := by
    simp only [map_ofNat]
    ring
  have hN : (X * (1 + 2 * X) : ℚ⟦X⟧) = X ^ 1 + C 2 * X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [hD, hN, show ∀ q : ℚ⟦X⟧, q * (1 - X ^ 1 - C 2 * X ^ 2 + X ^ 3 + X ^ 4) =
      q - q * X ^ 1 - C 2 * (q * X ^ 2) + q * X ^ 3 + q * X ^ 4 from fun q => by ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul]
  match n with
  | 0 => norm_num [coeff_mul_X_pow', coeff_mk, coeff_X_pow, coeff_X, S0]
  | 1 => norm_num [coeff_mul_X_pow', coeff_mk, coeff_X_pow, coeff_X, S0, S1]
  | 2 => norm_num [coeff_mul_X_pow', coeff_mk, coeff_X_pow, coeff_X, S0, S1, S2]
  | 3 => norm_num [coeff_mul_X_pow', coeff_mk, coeff_X_pow, coeff_X, S0, S1, S2, S3]
  | m + 4 =>
    have h0 : coeff (m + 4) (mk fun n => (S n : ℚ)) = ((S (m + 4) : ℕ) : ℚ) := coeff_mk _ _
    have h1 : coeff (m + 4) ((mk fun n => (S n : ℚ)) * (X : ℚ⟦X⟧) ^ 1) = ((S (m + 3) : ℕ) : ℚ) := by
      rw [show m + 4 = m + 3 + 1 from rfl, coeff_mul_X_pow, coeff_mk]
    have h2 : coeff (m + 4) ((mk fun n => (S n : ℚ)) * (X : ℚ⟦X⟧) ^ 2) = ((S (m + 2) : ℕ) : ℚ) := by
      rw [show m + 4 = m + 2 + 2 from rfl, coeff_mul_X_pow, coeff_mk]
    have h3 : coeff (m + 4) ((mk fun n => (S n : ℚ)) * (X : ℚ⟦X⟧) ^ 3) = ((S (m + 1) : ℕ) : ℚ) := by
      rw [show m + 4 = m + 1 + 3 from rfl, coeff_mul_X_pow, coeff_mk]
    have h4 : coeff (m + 4) ((mk fun n => (S n : ℚ)) * (X : ℚ⟦X⟧) ^ 4) = ((S (m) : ℕ) : ℚ) := by
      rw [coeff_mul_X_pow, coeff_mk]
    have e1 : coeff (m + 4) (X ^ 1 : ℚ⟦X⟧) = 0 := by
      rw [coeff_X_pow]
      split_ifs with h
      · omega
      · rfl
    have e2 : coeff (m + 4) (X ^ 2 : ℚ⟦X⟧) = 0 := by
      rw [coeff_X_pow]
      split_ifs with h
      · omega
      · rfl
    rw [h0, h1, h2, h3, h4, e1, e2]
    have q : ((S (m + 4) : ℕ) : ℚ) + S (m + 1) + S m = S (m + 3) + 2 * S (m + 2) := by
      exact_mod_cast S_rec m
    linarith

end R301653

open OMA.S_oeis_a301653 R301653 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a301653.main := by
  intro n
  have hc : constantCoeff ((1 - X) * (1 + X) * (1 - X - X ^ 2) : ℚ⟦X⟧) ≠ 0 := by simp
  have key := (eq_mul_inv_iff_mul_eq hc).mpr series_id
  unfold a
  rw [← key, coeff_mk]
  unfold S
  rw [Nat.cast_sum]
