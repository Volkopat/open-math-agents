import OMAStatements.S_oeis_a267068

/-!
Proof of both conjectures of A267068.
Credit: @rtflynn (agent: Claude Code, model claude-opus-5-5)

Let `Q 0 = 0`, `Q 1 = 1`, `Q (d+2) = Q (d+1) - X Q d` and `Lu 0 = 2`, `Lu 1 = 1`,
`Lu (d+2) = Lu (d+1) - X Lu d` (Fibonacci and Lucas polynomials in `-X`), and let `I` be the
linear functional `X^k ↦ 1/(k+1)` (the integral over `[0,1]`).
1. `c m d = (-1)^m I(X^m Q d)`, by the recurrence of `c` and of `Q`.
2. `derivative (Lu (n+1)) = -(n+1) Q n` and `I (derivative p) = p(1) - p(0)`, so
   `(n+1) B(0,n) = (n+1) I(Q n) = Lu (n+1) (0) - Lu (n+1) (1) = 1 - W (n+1)` with `W n = Lu n (1)`.
3. `W (n+3) = -W n`, so `(n+1) B(0,n)` is 6-periodic: 0, 2, 3, 2, 0, -1. Hence
   `a(6k) = 6k+1`, `a(6k+1) = 2`, `a(6k+2) = 3`, `a(6k+3) = 2`, `a(6k+4) = 6k+5`, `a(6k+5) = 1`,
   which gives the recurrence, and the generating function since its denominator is
   `(1 - x^6)^2`.
-/

namespace OMA.P_oeis_a267068

open Polynomial OMA.S_oeis_a267068

noncomputable def Q : ℕ → ℚ[X]
  | 0 => 0
  | 1 => 1
  | d + 2 => Q (d + 1) - X * Q d

noncomputable def Lu : ℕ → ℚ[X]
  | 0 => 2
  | 1 => 1
  | d + 2 => Lu (d + 1) - X * Lu d

lemma Q_ss (d : ℕ) : Q (d + 2) = Q (d + 1) - X * Q d := by rw [Q]

lemma Lu_ss (d : ℕ) : Lu (d + 2) = Lu (d + 1) - X * Lu d := by rw [Lu]

/-- The integral over `[0, 1]`, as a linear functional on polynomials. -/
noncomputable def I : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun k => (1 / ((k : ℚ) + 1)) • LinearMap.id)

lemma I_monomial (k : ℕ) (r : ℚ) : I (monomial k r) = r / ((k : ℚ) + 1) := by
  simp [I, Polynomial.lsum_apply, Polynomial.sum_monomial_index]
  ring

lemma I_X_pow (k : ℕ) : I (X ^ k) = 1 / ((k : ℚ) + 1) := by
  rw [X_pow_eq_monomial, I_monomial]

lemma c_eq : ∀ m d, c m d = (-1) ^ m * I (X ^ m * Q d)
  | m, 0 => by simp [c, Q]
  | m, 1 => by
    rw [c, Q, mul_one, I_X_pow, pow_add]
    ring
  | m, d + 2 => by
    rw [c, c_eq (m + 1) d, c_eq m (d + 1), Q_ss, mul_sub, map_sub,
      show (X : ℚ[X]) ^ m * (X * Q d) = X ^ (m + 1) * Q d by ring, pow_succ]
    ring

lemma I_derivative (p : ℚ[X]) : I (derivative p) = eval 1 p - eval 0 p := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    rw [map_add, map_add, hp, hq, eval_add, eval_add]
    ring
  · intro n r
    rcases n with _ | k
    · simp
    · rw [derivative_monomial, I_monomial]
      simp only [eval_monomial, one_pow, mul_one, Nat.add_sub_cancel]
      rw [zero_pow (Nat.succ_ne_zero k), mul_zero]
      push_cast
      field_simp
      simp

lemma Lu_aux : ∀ n, Lu (n + 1) = Q (n + 1) - 2 * X * Q n
  | 0 => by simp [Lu, Q]
  | 1 => by
    rw [Lu_ss, Q_ss]
    simp [Lu, Q]
    ring
  | n + 2 => by
    rw [Lu_ss, Lu_aux (n + 1), Lu_aux n, Q_ss (n + 1), Q_ss n]
    ring

lemma Lu_deriv : ∀ n, derivative (Lu (n + 1)) = -(((n + 1 : ℕ) : ℚ[X]) * Q n)
  | 0 => by simp [Lu, Q]
  | 1 => by
    rw [Lu_ss]
    simp [Lu, Q]
  | n + 2 => by
    rw [Lu_ss, derivative_sub, derivative_mul, derivative_X, Lu_deriv (n + 1), Lu_deriv n,
      Lu_aux n, Q_ss n]
    push_cast
    ring

lemma Lu_eval_zero : ∀ n, eval 0 (Lu (n + 1)) = 1
  | 0 => by simp [Lu]
  | n + 1 => by
    rw [Lu_ss, eval_sub, eval_mul, eval_X, zero_mul, sub_zero, Lu_eval_zero n]

/-- `W n = Lu n` at `1`. -/
noncomputable def W (n : ℕ) : ℚ := eval 1 (Lu n)

lemma W_three (n : ℕ) : W (n + 3) = -W n := by
  have h1 : Lu (n + 3) = Lu (n + 2) - X * Lu (n + 1) := Lu_ss (n + 1)
  have h2 : Lu (n + 2) = Lu (n + 1) - X * Lu n := Lu_ss n
  simp only [W, h1, h2, eval_sub, eval_mul, eval_X, one_mul]
  ring

lemma W_per (k j : ℕ) : W (6 * k + j) = W j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 6 * (k + 1) + j = 6 * k + j + 3 + 3 by ring, W_three, W_three, neg_neg, ih]

lemma W0 : W 0 = 2 := by simp [W, Lu]
lemma W1 : W 1 = 1 := by simp [W, Lu]
lemma W2 : W 2 = -1 := by
  have h : Lu 2 = Lu 1 - X * Lu 0 := Lu_ss 0
  simp only [W, h, eval_sub, eval_mul, eval_X, one_mul]
  simp [Lu]
  norm_num
lemma W3 : W 3 = -2 := by rw [show (3 : ℕ) = 0 + 3 from rfl, W_three, W0]
lemma W4 : W 4 = -1 := by rw [show (4 : ℕ) = 1 + 3 from rfl, W_three, W1]
lemma W5 : W 5 = 1 := by rw [show (5 : ℕ) = 2 + 3 from rfl, W_three, W2, neg_neg]
lemma W6 : W 6 = 2 := by rw [show (6 : ℕ) = 3 + 3 from rfl, W_three, W3, neg_neg]

lemma B_form (n : ℕ) : B 0 n = (1 - W (n + 1)) / ((n : ℚ) + 1) := by
  have hI : ((n : ℚ) + 1) * I (Q n) = 1 - W (n + 1) := by
    have h1 : ((n : ℚ) + 1) * I (Q n) = I (((n + 1 : ℕ) : ℚ[X]) * Q n) := by
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
      push_cast
      ring
    rw [h1, show ((n + 1 : ℕ) : ℚ[X]) * Q n = -derivative (Lu (n + 1)) by rw [Lu_deriv]; ring,
      map_neg, I_derivative, Lu_eval_zero, W]
    ring
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [B, Nat.sub_zero, c_eq, pow_zero, one_mul, pow_zero, one_mul, eq_div_iff hn, mul_comm, hI]

lemma den_inv (k : ℕ) (hk : k ≠ 0) : ((k : ℚ)⁻¹).den = k := by
  rw [Rat.inv_natCast_den, if_neg hk]

lemma a_0 (k : ℕ) : a (6 * k) = 6 * k + 1 := by
  have hB : B 0 (6 * k) = 0 := by
    rw [B_form, show 6 * k + 1 = 6 * k + 1 from rfl, W_per, W1]
    simp
  simp [a, A189733, hB]

lemma a_4 (k : ℕ) : a (6 * k + 4) = 6 * k + 5 := by
  have hB : B 0 (6 * k + 4) = 0 := by
    rw [B_form, show 6 * k + 4 + 1 = 6 * k + 5 from rfl, W_per, W5]
    simp
  simp [a, A189733, hB]
  ring

lemma a_1 (k : ℕ) : a (6 * k + 1) = 2 := by
  have hB : B 0 (6 * k + 1) = ((3 * k + 1 : ℕ) : ℚ)⁻¹ := by
    rw [B_form, show 6 * k + 1 + 1 = 6 * k + 2 from rfl, W_per, W2]
    push_cast
    field_simp
    ring
  simp only [a, A189733, hB, den_inv (3 * k + 1) (by omega)]
  push_cast
  field_simp
  ring

lemma a_2 (k : ℕ) : a (6 * k + 2) = 3 := by
  have hB : B 0 (6 * k + 2) = ((2 * k + 1 : ℕ) : ℚ)⁻¹ := by
    rw [B_form, show 6 * k + 2 + 1 = 6 * k + 3 from rfl, W_per, W3]
    push_cast
    field_simp
    ring
  simp only [a, A189733, hB, den_inv (2 * k + 1) (by omega)]
  push_cast
  field_simp
  ring

lemma a_3 (k : ℕ) : a (6 * k + 3) = 2 := by
  have hB : B 0 (6 * k + 3) = ((3 * k + 2 : ℕ) : ℚ)⁻¹ := by
    rw [B_form, show 6 * k + 3 + 1 = 6 * k + 4 from rfl, W_per, W4]
    push_cast
    field_simp
    ring
  simp only [a, A189733, hB, den_inv (3 * k + 2) (by omega)]
  push_cast
  field_simp
  ring

lemma a_5 (k : ℕ) : a (6 * k + 5) = 1 := by
  have hB : B 0 (6 * k + 5) = -((6 * k + 6 : ℕ) : ℚ)⁻¹ := by
    rw [B_form, show 6 * k + 5 + 1 = 6 * k + 6 from rfl, W_per, W6]
    push_cast
    field_simp
    ring
  simp only [a, A189733, hB, Rat.neg_den, den_inv (6 * k + 6) (by omega)]
  push_cast
  field_simp
  ring

lemma recur (n : ℕ) (hn : 11 < n) : a n = 2 * a (n - 6) - a (n - 12) := by
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 6 ∧ n = 6 * k + r + 12 :=
    ⟨(n - 12) / 6, (n - 12) % 6, Nat.mod_lt _ (by norm_num), by omega⟩
  rw [show 6 * k + r + 12 - 6 = 6 * (k + 1) + r by omega,
    show 6 * k + r + 12 - 12 = 6 * k + r by omega,
    show 6 * k + r + 12 = 6 * (k + 2) + r by omega]
  interval_cases r
  · simp only [Nat.add_zero, a_0]; push_cast; ring
  · simp only [a_1]; ring
  · simp only [a_2]; ring
  · simp only [a_3]; ring
  · simp only [a_4]; push_cast; ring
  · simp only [a_5]; ring

end OMA.P_oeis_a267068

open OMA.P_oeis_a267068 in
theorem OMA.solution : type_of% @OMA.S_oeis_a267068.main := by
  refine ⟨recur, ?_⟩
  set A := PowerSeries.mk OMA.S_oeis_a267068.a with hAdef
  have hD : A * ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 *
        (1 - PowerSeries.X + PowerSeries.X ^ 2) ^ 2 * (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 2) =
      (A + A * PowerSeries.X ^ 12) - 2 • (A * PowerSeries.X ^ 6) := by
    ring
  have hN : (1 + 2 * PowerSeries.X + 3 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
        5 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5 + 5 * PowerSeries.X ^ 6 -
        2 * PowerSeries.X ^ 7 - 3 * PowerSeries.X ^ 8 - 2 * PowerSeries.X ^ 9 +
        PowerSeries.X ^ 10 - PowerSeries.X ^ 11 : PowerSeries ℚ) =
      (PowerSeries.X ^ 0 + 2 • PowerSeries.X ^ 1 + 3 • PowerSeries.X ^ 2 +
          2 • PowerSeries.X ^ 3 + 5 • PowerSeries.X ^ 4 + PowerSeries.X ^ 5 +
          5 • PowerSeries.X ^ 6 + PowerSeries.X ^ 10) -
        (2 • PowerSeries.X ^ 7 + 3 • PowerSeries.X ^ 8 + 2 • PowerSeries.X ^ 9 +
          PowerSeries.X ^ 11) := by
    ring
  rw [hD, hN]
  ext n
  simp only [map_add, map_sub, map_nsmul]
  simp only [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow, hAdef, PowerSeries.coeff_mk,
    nsmul_eq_mul]
  rcases lt_or_ge n 12 with hn | hn
  · have t0 : OMA.S_oeis_a267068.a 0 = 1 := by simpa using a_0 0
    have t1 : OMA.S_oeis_a267068.a 1 = 2 := by simpa using a_1 0
    have t2 : OMA.S_oeis_a267068.a 2 = 3 := by simpa using a_2 0
    have t3 : OMA.S_oeis_a267068.a 3 = 2 := by simpa using a_3 0
    have t4 : OMA.S_oeis_a267068.a 4 = 5 := by simpa using a_4 0
    have t5 : OMA.S_oeis_a267068.a 5 = 1 := by simpa using a_5 0
    have t6 : OMA.S_oeis_a267068.a 6 = 7 := by have h := a_0 1; norm_num at h; exact h
    have t7 : OMA.S_oeis_a267068.a 7 = 2 := by simpa using a_1 1
    have t8 : OMA.S_oeis_a267068.a 8 = 3 := by simpa using a_2 1
    have t9 : OMA.S_oeis_a267068.a 9 = 2 := by simpa using a_3 1
    have t10 : OMA.S_oeis_a267068.a 10 = 11 := by have h := a_4 1; norm_num at h; exact h
    have t11 : OMA.S_oeis_a267068.a 11 = 1 := by simpa using a_5 1
    interval_cases n <;> simp [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11] <;> norm_num
  · have h := recur n (by omega)
    have e6 : 6 ≤ n := by omega
    have e12 : 12 ≤ n := hn
    simp only [e6, e12, if_true, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega,
      show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega,
      show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega,
      show n ≠ 11 by omega, if_false]
    rw [h]
    push_cast
    ring
