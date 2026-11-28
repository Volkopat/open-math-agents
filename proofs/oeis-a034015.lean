import OMAStatements.S_oeis_a034015

namespace P034015
open OMA.S_oeis_a034015 Polynomial Finset


noncomputable abbrev Q : ℚ[X] := (X + 1) ^ 2 * ((X + 1) + 1)

lemma inner (i n : ℕ) : ∑ j ∈ range (i + 1), (i.choose j : ℚ) * ((2 * i + j).choose n : ℚ) =
    (Q ^ i).coeff n := by
  rw [Q, mul_pow, add_pow (X + 1 : ℚ[X]) 1 i, mul_sum, finsetSum_coeff]
  refine sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one, ← mul_assoc, ← pow_mul, ← pow_add, coeff_mul_natCast, coeff_X_add_one_pow]
  ring

lemma outer (n : ℕ) : ∑ i ∈ range (n + 1), (Q ^ i).coeff n * (-2 : ℚ) ^ (n - i) *
    ((n + 1).choose i : ℚ) = (Q ^ (n + 1)).coeff n / 2 := by
  have h0 : ((Q + C (-2)) ^ (n + 1)).coeff n = 0 := by
    have : Q + C (-2) = X * (X ^ 2 + 4 * X + 5) := by
      simp only [Q, map_neg, C_ofNat]
      ring
    rw [this, mul_pow, coeff_X_pow_mul']
    simp
  rw [add_pow, finsetSum_coeff, sum_range_succ] at h0
  simp only [← C_pow, coeff_mul_natCast, coeff_mul_C, Nat.sub_self, pow_zero, mul_one,
    Nat.choose_self, Nat.cast_one] at h0
  have h1 : ∑ i ∈ range (n + 1), (Q ^ i).coeff n * (-2 : ℚ) ^ (n + 1 - i) *
      ((n + 1).choose i : ℚ) = -2 * ∑ i ∈ range (n + 1), (Q ^ i).coeff n * (-2 : ℚ) ^ (n - i) *
      ((n + 1).choose i : ℚ) := by
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [show n + 1 - i = n - i + 1 by omega, pow_succ]
    ring
  rw [h1] at h0
  linarith

lemma top (n : ℕ) : (Q ^ (n + 1)).coeff n = ∑ k ∈ range (n + 1),
    ((2 * n + 2).choose k : ℚ) * (2 ^ (k + 1) * ((n + 1).choose (k + 1) : ℚ)) := by
  have hQ : Q ^ (n + 1) = (X + 1) ^ (2 * n + 2) * (X + C 2) ^ (n + 1) := by
    rw [Q, mul_pow, ← pow_mul, add_assoc, show (1 : ℚ[X]) + 1 = C 2 by rw [← C_1, ← C_add]; norm_num]
    ring_nf
  rw [hQ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  rw [coeff_X_add_one_pow, coeff_X_add_C_pow, show n + 1 - (n - k) = k + 1 by omega,
    Nat.choose_symm_of_eq_add (show n + 1 = (n - k) + (k + 1) by omega)]

theorem main' (n : ℕ) : a n = ∑ i ∈ range (n + 1), ∑ j ∈ range (i + 1),
    (-2 : ℚ) ^ (n - i) * (i.choose j : ℚ) * ((2 * i + j).choose n : ℚ) * ((n + 1).choose i : ℚ) /
      (n + 1) := by
  have hR : ∑ i ∈ range (n + 1), ∑ j ∈ range (i + 1), (-2 : ℚ) ^ (n - i) * (i.choose j : ℚ) *
      ((2 * i + j).choose n : ℚ) * ((n + 1).choose i : ℚ) / (n + 1) =
      (∑ i ∈ range (n + 1), (Q ^ i).coeff n * (-2 : ℚ) ^ (n - i) * ((n + 1).choose i : ℚ)) /
        (n + 1) := by
    rw [sum_div]
    refine sum_congr rfl fun i _ => ?_
    rw [← inner, sum_mul, sum_mul, sum_div]
    refine sum_congr rfl fun j _ => ?_
    ring
  rw [hR, outer, top, a, div_div, sum_div]
  refine sum_congr rfl fun k _ => ?_
  have h := Nat.add_one_mul_choose_eq n k
  have h' : ((n : ℚ) + 1) * (n.choose k : ℚ) = ((n + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
    exact_mod_cast h
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (2 : ℚ) ^ (k + 1) * ((2 * n + 2).choose k : ℚ) * h'

end P034015

theorem OMA.solution : type_of% @OMA.S_oeis_a034015.main := by
  intro n
  exact P034015.main' n
