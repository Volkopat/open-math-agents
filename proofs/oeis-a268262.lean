import OMAStatements.S_oeis_a268262

-- Problem: A268262, length-four arrays over 0..n whose new repeated values appear in order 0, 1, 2, ...
-- Credit: @mattdorman (the owner of the agent is credited as the solver)
--
-- Proof. Split the count by which adjacent pairs (a, b), (b, c), (c, d) are equal. With no equal
-- pair the list of repeats is empty: (n+1) n^3 arrays. With exactly one equal pair its value must
-- be 0: n^2 arrays for each of the three pairs. With a = b = c or b = c = d (and the third pair
-- unequal) the common value is 0: n arrays each. With a = b and c = d but b ≠ c the values must
-- be 0 then 1: one array. All four equal forces 0: one array. In total
-- (n+1) n^3 + 3 n^2 + 2 n + 2 = n^4 + n^3 + 3 n^2 + 2 n + 2 (n ≥ 1).
-- `ind_eq` writes the indicator as the sum of these eight pattern indicators, and `box_sum`
-- sums them over any finite set containing 0 and 1. The recurrence and the generating function
-- follow from the quartic closed form: its fifth difference vanishes, and the first six
-- coefficients of (1 - x)^5 A(x) are 0, 9, -3, 23, -7, 2.

namespace OMA.A268262
open OMA.S_oeis_a268262

/-- The indicator `[x = y]`. -/
def δ (x y : ℕ) : ℚ := if x = y then 1 else 0

theorem ind_eq (a b c d : ℕ) :
    (if sequential 0 (repeats a b c d) then (1 : ℚ) else 0) =
      (1 - δ a b) * (1 - δ b c) * (1 - δ c d)
      + δ a b * δ a 0 * (1 - δ b c) * (1 - δ c d)
      + (1 - δ a b) * δ b c * δ b 0 * (1 - δ c d)
      + (1 - δ a b) * (1 - δ b c) * δ c d * δ c 0
      + δ a b * δ b c * δ a 0 * (1 - δ c d)
      + (1 - δ a b) * δ b c * δ c d * δ b 0
      + δ a b * (1 - δ b c) * δ c d * δ a 0 * δ c 1
      + δ a b * δ b c * δ c d * δ a 0 := by
  unfold δ
  rcases (by omega : a = 0 ∨ a = 1 ∨ 2 ≤ a) with ha | ha | ha <;>
  rcases (by omega : b = 0 ∨ b = 1 ∨ 2 ≤ b) with hb | hb | hb <;>
  rcases (by omega : c = 0 ∨ c = 1 ∨ 2 ≤ c) with hc | hc | hc <;>
  by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hcd : c = d <;>
  simp_all [repeats, sequential] <;> (first | omega | (split_ifs <;> first | rfl | (exfalso; omega)))

theorem box_sum (s : Finset ℕ) (h0 : 0 ∈ s) (h1 : 1 ∈ s) :
    (∑ b ∈ s, ∑ a ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      (if sequential 0 (repeats a b c d) then (1 : ℚ) else 0)) =
      ((s.card : ℚ) - 1) ^ 4 + ((s.card : ℚ) - 1) ^ 3 + 3 * ((s.card : ℚ) - 1) ^ 2 +
        2 * ((s.card : ℚ) - 1) + 2 := by
  simp only [ind_eq, δ]
  simp only [mul_sub, mul_one, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_mem,
    Finset.inter_self, Finset.sum_ite_irrel, h0, h1, if_true]
  norm_num
  ring

theorem count_eq (n : ℕ) (hn : 0 < n) :
    count n = (n:ℚ)^4 + n^3 + 3*n^2 + 2*n + 2 := by
  unfold count
  rw [box_sum (Finset.range (n + 1)) (by simp) (by simp; omega), Finset.card_range]
  push_cast
  ring

theorem terms_zero : terms 0 = 0 := rfl

theorem terms_succ (n : ℕ) :
    terms (n + 1) = ((n:ℚ)+1)^4 + (n+1)^3 + 3*(n+1)^2 + 2*(n+1) + 2 := by
  rw [terms, count_eq (n + 1) (by omega)]
  push_cast
  ring

open PowerSeries in
theorem gf : (1 - X) ^ 5 * mk terms = (X * (9 - 3*X + 23*X^2 - 7*X^3 + 2*X^4) : PowerSeries ℚ) := by
  set A := mk terms with hA
  have hl : (1 - X) ^ 5 * A =
      A - C (5:ℚ) * (A * X ^ 1) + C (10:ℚ) * (A * X ^ 2) - C (10:ℚ) * (A * X ^ 3) +
        C (5:ℚ) * (A * X ^ 4) - A * X ^ 5 := by
    simp only [map_ofNat]
    ring
  have hr : (X * (9 - 3*X + 23*X^2 - 7*X^3 + 2*X^4) : PowerSeries ℚ) =
      C (9:ℚ) * X ^ 1 - C (3:ℚ) * X ^ 2 + C (23:ℚ) * X ^ 3 - C (7:ℚ) * X ^ 4 + C (2:ℚ) * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [hl, hr, hA]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | m
  all_goals try (simp [terms_zero, terms_succ, coeff_C] <;> norm_num <;> done)
  · have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = (m + 4) + 1 := by omega
    have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = (m + 3) + 1 := by omega
    have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = (m + 2) + 1 := by omega
    have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = (m + 1) + 1 := by omega
    have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := by omega
    have e0 : m + 1 + 1 + 1 + 1 + 1 + 1 = (m + 5) + 1 := by omega
    simp only [e1, e2, e3, e4, e5, show 1 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 2 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega, show 3 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      show 4 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega, show 5 ≤ m + 1 + 1 + 1 + 1 + 1 + 1 by omega,
      if_true, show m + 1 + 1 + 1 + 1 + 1 + 1 ≠ 2 by omega,
      show m + 1 + 1 + 1 + 1 + 1 + 1 ≠ 4 by omega,
      if_false, coeff_C, Nat.add_one_ne_zero]
    rw [e0, terms_succ, terms_succ, terms_succ, terms_succ, terms_succ, terms_succ]
    push_cast
    ring

theorem recurrence (n : ℕ) : terms (n+6) = 5*terms (n+5) - 10*terms (n+4) +
    10*terms (n+3) - 5*terms (n+2) + terms (n+1) := by
  rw [show n + 6 = (n + 5) + 1 by omega, show n + 5 = (n + 4) + 1 by omega,
    show n + 4 = (n + 3) + 1 by omega, show n + 3 = (n + 2) + 1 by omega,
    show n + 2 = (n + 1) + 1 by omega]
  simp only [terms_succ]
  push_cast
  ring

end OMA.A268262

theorem OMA.solution : type_of% @OMA.S_oeis_a268262.main :=
  ⟨OMA.A268262.count_eq, OMA.A268262.recurrence, OMA.A268262.gf⟩
