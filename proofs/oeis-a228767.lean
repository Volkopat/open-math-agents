import OMAStatements.S_oeis_a228767

-- Problem: oeis-a228767
-- Upstream: statements/oeis-a228767.lean (declaration OMA.S_oeis_a228767.main)
--
-- Proof. Write B_k for the k-th Bernoulli polynomial.
-- 1. For every rational x: sum_{k <= m+1} C(m+1,k) B_k(x) = (m+1) x^m + B_{m+1}(x)
--    (Polynomial.sum_bernoulli evaluated at x, plus the last term).
-- 2. In `transformed (m+1)` the two signs multiply to (-1)^(m+1), so
--    transformed (m+1) = (-1)^(m+1) ((m+1) + B_{m+1}(1) + (m+1) 2^m + B_{m+1}(2)) / 2.
-- 3. For odd n = 2k+3: B_n(1) = 0 and B_n(2) = B_n(1) + n, which gives the closed form
--    term (k+2) = -(2k+3)(1 + 2 * 4^k).
-- 4. The generating function identity is checked coefficient by coefficient:
--    degrees 0 to 5 by the first values 0, -2, -9, -45, -231, -1161, and degree m+6 by
--    the closed form, which the operator (E-1)^2 (E-4)^2 annihilates.

namespace A228767Proof

theorem sum_choose_bernoulli_eval (m : ℕ) (x : ℚ) :
    ∑ k ∈ Finset.range (m + 1 + 1), ((m + 1).choose k : ℚ) * (Polynomial.bernoulli k).eval x =
      (m + 1 : ℚ) * x ^ m + (Polynomial.bernoulli (m + 1)).eval x := by
  have h := congrArg (Polynomial.eval x) (Polynomial.sum_bernoulli m)
  rw [Polynomial.eval_finsetSum] at h
  simp only [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_monomial] at h
  rw [Finset.sum_range_succ, h, Nat.choose_self, Nat.cast_one, one_mul]

theorem transformed_succ (m : ℕ) :
    OMA.S_oeis_a228767.transformed (m + 1) =
      (-1 : ℚ) ^ (m + 1) * ((m + 1 : ℚ) + (Polynomial.bernoulli (m + 1)).eval 1
        + (m + 1 : ℚ) * 2 ^ m + (Polynomial.bernoulli (m + 1)).eval 2) / 2 := by
  have h1 := sum_choose_bernoulli_eval m 1
  have h2 := sum_choose_bernoulli_eval m 2
  rw [one_pow, mul_one] at h1
  have key : ∀ k ∈ Finset.range (m + 1 + 1),
      (-1 : ℚ) ^ (m + 1 - k) * ((m + 1).choose k : ℚ) * OMA.S_oeis_a228767.input k =
      (-1 : ℚ) ^ (m + 1) / 2 * (((m + 1).choose k : ℚ) * (Polynomial.bernoulli k).eval 1 +
        ((m + 1).choose k : ℚ) * (Polynomial.bernoulli k).eval 2) := by
    intro k hk
    have hk' : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hp : (-1 : ℚ) ^ (m + 1) = (-1 : ℚ) ^ (m + 1 - k) * (-1 : ℚ) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk']
    rw [hp]
    unfold OMA.S_oeis_a228767.input
    ring
  unfold OMA.S_oeis_a228767.transformed
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_add_distrib, h1, h2]
  ring

theorem term_zero : OMA.S_oeis_a228767.term 0 = 0 := rfl

theorem term_one : OMA.S_oeis_a228767.term 1 = -2 := by
  show OMA.S_oeis_a228767.transformed (0 + 1) = -2
  rw [transformed_succ]
  norm_num [Polynomial.bernoulli_one]

theorem term_two_add (k : ℕ) :
    OMA.S_oeis_a228767.term (k + 2) = (8 + 4 ^ (k + 2)) * (1 - 2 * ((k : ℚ) + 2)) / 8 := by
  show OMA.S_oeis_a228767.transformed (2 * (k + 1) + 1) = _
  have e : 2 * (k + 1) + 1 = (2 * k + 2) + 1 := by ring
  rw [e, transformed_succ]
  have hodd : Odd (2 * k + 2 + 1) := ⟨k + 1, by ring⟩
  have hb1 : (Polynomial.bernoulli (2 * k + 2 + 1)).eval (1 : ℚ) = 0 := by
    rw [Polynomial.bernoulli_eval_one]
    exact bernoulli'_eq_zero_of_odd hodd (by omega)
  have hb2 : (Polynomial.bernoulli (2 * k + 2 + 1)).eval (2 : ℚ) = ((2 * k + 2 + 1 : ℕ) : ℚ) := by
    have h := Polynomial.bernoulli_eval_one_add (2 * k + 2 + 1) (1 : ℚ)
    rw [hb1, one_pow, mul_one, zero_add] at h
    have h11 : (1 : ℚ) + 1 = 2 := by norm_num
    rw [h11] at h
    exact h
  have hs : (-1 : ℚ) ^ (2 * k + 2 + 1) = -1 := hodd.neg_one_pow
  have h22 : (2 : ℚ) ^ (2 * k) = 4 ^ k := by
    rw [pow_mul]
    norm_num
  have h4 : (4 : ℚ) ^ (k + 2) = 16 * 4 ^ k := by
    rw [pow_add]
    ring
  have h2 : (2 : ℚ) ^ (2 * k + 2) = 4 * 4 ^ k := by
    rw [pow_add, h22]
    ring
  rw [hb1, hb2, hs, h4, h2]
  push_cast
  ring

theorem term_two : OMA.S_oeis_a228767.term 2 = -9 := by
  have h := term_two_add 0
  norm_num at h
  exact h

theorem term_three : OMA.S_oeis_a228767.term 3 = -45 := by
  have h := term_two_add 1
  norm_num at h
  exact h

theorem term_four : OMA.S_oeis_a228767.term 4 = -231 := by
  have h := term_two_add 2
  norm_num at h
  exact h

theorem term_five : OMA.S_oeis_a228767.term 5 = -1161 := by
  have h := term_two_add 3
  norm_num at h
  exact h

theorem gf :
    (1 - PowerSeries.X) ^ 2 * (1 - 4 * PowerSeries.X) ^ 2 *
        PowerSeries.mk OMA.S_oeis_a228767.term =
      (-PowerSeries.X * (2 - 11 * PowerSeries.X + 21 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3
        + 8 * PowerSeries.X ^ 4) : PowerSeries ℚ) := by
  have hL : (1 - PowerSeries.X) ^ 2 * (1 - 4 * PowerSeries.X) ^ 2 *
        PowerSeries.mk OMA.S_oeis_a228767.term =
      PowerSeries.C (1 : ℚ) * (PowerSeries.X ^ 0 * PowerSeries.mk OMA.S_oeis_a228767.term)
      + PowerSeries.C (-10 : ℚ) * (PowerSeries.X ^ 1 * PowerSeries.mk OMA.S_oeis_a228767.term)
      + PowerSeries.C (33 : ℚ) * (PowerSeries.X ^ 2 * PowerSeries.mk OMA.S_oeis_a228767.term)
      + PowerSeries.C (-40 : ℚ) * (PowerSeries.X ^ 3 * PowerSeries.mk OMA.S_oeis_a228767.term)
      + PowerSeries.C (16 : ℚ) * (PowerSeries.X ^ 4 * PowerSeries.mk OMA.S_oeis_a228767.term) := by
    simp only [map_neg, map_ofNat, map_one]
    ring
  have hR : (-PowerSeries.X * (2 - 11 * PowerSeries.X + 21 * PowerSeries.X ^ 2
        - 2 * PowerSeries.X ^ 3 + 8 * PowerSeries.X ^ 4) : PowerSeries ℚ) =
      PowerSeries.C (-2 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (11 : ℚ) * PowerSeries.X ^ 2
      + PowerSeries.C (-21 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 4
      + PowerSeries.C (-8 : ℚ) * PowerSeries.X ^ 5 := by
    simp only [map_neg, map_ofNat]
    ring
  rw [hL, hR]
  ext n
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_mk]
  rcases lt_or_ge n 6 with h | h
  · interval_cases n <;>
      norm_num [term_zero, term_one, term_two, term_three, term_four, term_five]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    have c0 : 0 ≤ 6 + m := by omega
    have c1 : 1 ≤ 6 + m := by omega
    have c2 : 2 ≤ 6 + m := by omega
    have c3 : 3 ≤ 6 + m := by omega
    have c4 : 4 ≤ 6 + m := by omega
    have d1 : ¬ 6 + m = 1 := by omega
    have d2 : ¬ 6 + m = 2 := by omega
    have d3 : ¬ 6 + m = 3 := by omega
    have d4 : ¬ 6 + m = 4 := by omega
    have d5 : ¬ 6 + m = 5 := by omega
    have e0 : 6 + m - 0 = m + 4 + 2 := by omega
    have e1 : 6 + m - 1 = m + 3 + 2 := by omega
    have e2 : 6 + m - 2 = m + 2 + 2 := by omega
    have e3 : 6 + m - 3 = m + 1 + 2 := by omega
    have e4 : 6 + m - 4 = m + 2 := by omega
    rw [if_pos c0, if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_neg d1, if_neg d2, if_neg d3,
      if_neg d4, if_neg d5, e0, e1, e2, e3, e4, term_two_add, term_two_add, term_two_add,
      term_two_add, term_two_add]
    push_cast
    ring

end A228767Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a228767.main :=
  ⟨A228767Proof.term_one, A228767Proof.term_two_add, A228767Proof.gf⟩
