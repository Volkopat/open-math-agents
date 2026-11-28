import OMAStatements.S_oeis_a225887
import Mathlib

/-!
# OEIS A225887: Mathar-type recurrence for a convolution-defined sequence

`a(0) = 1`, `a(1) = 4`, `a(n+2) = 5 a(n+1) - ∑_{k ≤ n+1} a(k) a(n+1-k) + 6 ∑_{k ≤ n} a(k) a(n-k)`.

Let `A = ∑ a(n) xⁿ`. The defining rule, read coefficient by coefficient, is the quadratic equation

  `U A² - V A + N = 0`,  `U = 6*x**2 - x`,  `V = 1 - 5*x`,  `N = 1`.

Differentiating it and eliminating `A²` and `A³` with the equation itself gives a first order
linear differential equation `p A' + q A = r` with polynomial coefficients, and comparing the
coefficients of `xⁿ` beyond the degree of `r` gives the conjectured recurrence.
-/

open PowerSeries OMA.S_oeis_a225887

namespace OMA.A225887

/-- The generating function `A = ∑ a(n) xⁿ`. -/
noncomputable def A : ℤ⟦X⟧ := PowerSeries.mk a

/-- Its derivative `A'`. -/
noncomputable def B : ℤ⟦X⟧ := PowerSeries.derivative ℤ A

/-! ### Coefficient bookkeeping -/

lemma coeff_intCast (c : ℤ) (n : ℕ) :
    coeff n ((c : ℤ) : ℤ⟦X⟧) = if n = 0 then c else 0 := by
  rw [← eq_intCast (C : ℤ →+* ℤ⟦X⟧) c, coeff_C]

lemma coeff_intCast_mul (c : ℤ) (φ : ℤ⟦X⟧) (n : ℕ) :
    coeff n (((c : ℤ) : ℤ⟦X⟧) * φ) = c * coeff n φ := by
  rw [← eq_intCast (C : ℤ →+* ℤ⟦X⟧) c, coeff_C_mul]

/-- The coefficient of `xⁿ` in `c xⁱ φ`. -/
lemma coeff_term' (c : ℤ) (i n : ℕ) (φ : ℤ⟦X⟧) :
    coeff n (((c : ℤ) : ℤ⟦X⟧) * X ^ i * φ) = if i ≤ n then c * coeff (n - i) φ else 0 := by
  rw [mul_assoc, coeff_intCast_mul, coeff_X_pow_mul']
  split_ifs <;> simp

lemma coeff_term (c : ℤ) (i n : ℕ) (φ : ℤ⟦X⟧) (h : i ≤ n) :
    coeff n (((c : ℤ) : ℤ⟦X⟧) * X ^ i * φ) = c * coeff (n - i) φ := by
  rw [coeff_term', if_pos h]

lemma coeff_A (n : ℕ) : coeff n A = a n := coeff_mk n a

lemma coeff_B (n : ℕ) : coeff n B = a (n + 1) * ((n : ℤ) + 1) := by
  unfold B
  rw [coeff_derivative, coeff_A]

/-- The coefficient of `xⁿ` in `c xⁱ A'`, also valid at the edge `i = n + 1`. -/
lemma coeff_term_B (c : ℤ) (i n : ℕ) (h : i ≤ n + 1) :
    coeff n (((c : ℤ) : ℤ⟦X⟧) * X ^ i * B) = c * (a (n + 1 - i) * ((n : ℤ) + 1 - i)) := by
  rcases Nat.lt_or_ge n i with hlt | hle
  · have hi : i = n + 1 := by omega
    rw [mul_assoc, coeff_intCast_mul, coeff_X_pow_mul', if_neg (by omega), hi]
    push_cast
    ring
  · rw [coeff_term _ _ _ _ hle, coeff_B, show n - i + 1 = n + 1 - i by omega]
    push_cast [Nat.cast_sub hle]
    ring

/-- The coefficients of `A²` are the convolution sums. -/
lemma coeff_sq (m : ℕ) : coeff m (A * A) = ∑ k : Fin (m + 1), a k * a (m - k) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j A),
    Fin.sum_univ_eq_sum_range (fun k => a k * a (m - k)) (m + 1)]
  simp only [coeff_A]

/-! ### The quadratic equation -/

/-- `S1 = ∑ a(n+1) xⁿ`. -/
noncomputable def S1 : ℤ⟦X⟧ := PowerSeries.mk fun n => a (n + 1)

/-- `S2 = ∑ a(n+2) xⁿ`. -/
noncomputable def S2 : ℤ⟦X⟧ := PowerSeries.mk fun n => a (n + 2)

lemma a_0 : a 0 = 1 := by rw [a]

lemma a_1 : a 1 = 4 := by rw [a]

lemma hS1 : X * S1 = A - ((1 : ℤ) : ℤ⟦X⟧) := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_X_mul, map_sub, coeff_intCast, if_pos rfl]
    simp [A, a_0]
  · rw [coeff_succ_X_mul, map_sub, coeff_intCast, if_neg (Nat.succ_ne_zero n), sub_zero]
    simp [A, S1]

lemma hS2 : X * S2 = S1 - ((4 : ℤ) : ℤ⟦X⟧) := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_X_mul, map_sub, coeff_intCast, if_pos rfl]
    simp [S1, a_1]
  · rw [coeff_succ_X_mul, map_sub, coeff_intCast, if_neg (Nat.succ_ne_zero n), sub_zero]
    simp [S1, S2]

/-- `C₁ = ∑ [x^(n+1)] A² · xⁿ`. -/
noncomputable def C1 : ℤ⟦X⟧ := PowerSeries.mk fun n => coeff (n + 1) (A * A)

lemma hC1 : X * C1 = A * A - ((1 : ℤ) : ℤ⟦X⟧) := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_X_mul, map_sub, coeff_intCast, if_pos rfl, coeff_sq]
    simp [a_0]
  · rw [coeff_succ_X_mul, map_sub, coeff_intCast, if_neg (Nat.succ_ne_zero n), sub_zero]
    simp [C1]

/-- The defining rule as an identity of power series. -/
lemma hrec : S2 = ((5 : ℤ) : ℤ⟦X⟧) * S1 - C1 + ((6 : ℤ) : ℤ⟦X⟧) * (A * A) := by
  ext n
  simp only [map_add, map_sub, coeff_intCast_mul, S1, S2, C1, coeff_mk, coeff_sq]
  conv_lhs => rw [a]

/-- `U A² - V A + N = 0`. -/
lemma hE0 :
    ((((-1) : ℤ) : ℤ⟦X⟧) * (X) + ((6 : ℤ) : ℤ⟦X⟧) * (X * X)) * (A * A) - (((1 : ℤ) : ℤ⟦X⟧) + (((-5) : ℤ) : ℤ⟦X⟧) * (X)) * A + (((1 : ℤ) : ℤ⟦X⟧)) = 0 := by
  linear_combination (norm := (push_cast; ring))
    (-(X * X)) * hrec + X * hS2 + (1 - 5 * X) * hS1 + X * hC1

/-! ### The differential equation

Differentiating `U A² - V A + N = 0` and eliminating `A²`, `A³` with the equation itself gives a
first order linear differential equation; after cancelling the common polynomial factor it reads

  `p A' + q A = r`,
  `p = -6*x**4 + 37*x**3 - 12*x**2 + x`,
  `q = -6*x**3 + 54*x**2 - 15*x + 1`,
  `r = 1 - 7*x`.

Comparing the coefficients of `xⁿ` for `n ≥ 3` gives `(n + 1) a(n-0), (-3*(4*n + 1)) a(n-1), (37*n - 20) a(n-2), (-6*(n - 2)) a(n-3) = 0`.
-/

/-- The derivative of the quadratic equation. -/
lemma hE1 :
    ((((-1) : ℤ) : ℤ⟦X⟧) + ((12 : ℤ) : ℤ⟦X⟧) * (X)) * (A * A) + 2 * ((((-1) : ℤ) : ℤ⟦X⟧) * (X) + ((6 : ℤ) : ℤ⟦X⟧) * (X * X)) * A * B
      - ((((-5) : ℤ) : ℤ⟦X⟧)) * A - (((1 : ℤ) : ℤ⟦X⟧) + (((-5) : ℤ) : ℤ⟦X⟧) * (X)) * B
      + (((0 : ℤ) : ℤ⟦X⟧)) = 0 := by
  have h := congrArg (PowerSeries.derivative ℤ) hE0
  simp only [map_add, map_sub, map_zero, Derivation.leibniz, Derivation.map_intCast,
    PowerSeries.derivative_X, smul_eq_mul] at h
  unfold B
  linear_combination (norm := (push_cast; ring)) h

/-- `p A' + q A = r`. -/
lemma hODE :
    (((1 : ℤ) : ℤ⟦X⟧) * X ^ 1 + (((-12) : ℤ) : ℤ⟦X⟧) * X ^ 2 + ((37 : ℤ) : ℤ⟦X⟧) * X ^ 3 + (((-6) : ℤ) : ℤ⟦X⟧) * X ^ 4) * B
      + (((1 : ℤ) : ℤ⟦X⟧) + (((-15) : ℤ) : ℤ⟦X⟧) * X ^ 1 + ((54 : ℤ) : ℤ⟦X⟧) * X ^ 2 + (((-6) : ℤ) : ℤ⟦X⟧) * X ^ 3) * A
      - (((1 : ℤ) : ℤ⟦X⟧) + (((-7) : ℤ) : ℤ⟦X⟧) * X ^ 1) = 0 := by
  have h0 : ((((-1) : ℤ) : ℤ⟦X⟧) * X ^ 0 * (1 : ℤ⟦X⟧)) * ((((1 : ℤ) : ℤ⟦X⟧) * X ^ 1 + (((-12) : ℤ) : ℤ⟦X⟧) * X ^ 2 + ((37 : ℤ) : ℤ⟦X⟧) * X ^ 3 + (((-6) : ℤ) : ℤ⟦X⟧) * X ^ 4) * B
      + (((1 : ℤ) : ℤ⟦X⟧) + (((-15) : ℤ) : ℤ⟦X⟧) * X ^ 1 + ((54 : ℤ) : ℤ⟦X⟧) * X ^ 2 + (((-6) : ℤ) : ℤ⟦X⟧) * X ^ 3) * A
      - (((1 : ℤ) : ℤ⟦X⟧) + (((-7) : ℤ) : ℤ⟦X⟧) * X ^ 1)) = 0 := by
    linear_combination (norm := (push_cast; ring))
      (((((-1) : ℤ) : ℤ⟦X⟧) * (X) + ((6 : ℤ) : ℤ⟦X⟧) * (X * X)) * (2 * ((((-1) : ℤ) : ℤ⟦X⟧) * (X) + ((6 : ℤ) : ℤ⟦X⟧) * (X * X)) * A - (((1 : ℤ) : ℤ⟦X⟧) + (((-5) : ℤ) : ℤ⟦X⟧) * (X)))) * hE1
      + (-4 * ((((-1) : ℤ) : ℤ⟦X⟧) * (X) + ((6 : ℤ) : ℤ⟦X⟧) * (X * X)) ^ 2 * B - 2 * ((((-1) : ℤ) : ℤ⟦X⟧) * (X) + ((6 : ℤ) : ℤ⟦X⟧) * (X * X)) * ((((-1) : ℤ) : ℤ⟦X⟧) + ((12 : ℤ) : ℤ⟦X⟧) * (X)) * A
          - ((((-1) : ℤ) : ℤ⟦X⟧) + ((12 : ℤ) : ℤ⟦X⟧) * (X)) * (((1 : ℤ) : ℤ⟦X⟧) + (((-5) : ℤ) : ℤ⟦X⟧) * (X)) + 2 * ((((-1) : ℤ) : ℤ⟦X⟧) * (X) + ((6 : ℤ) : ℤ⟦X⟧) * (X * X)) * ((((-5) : ℤ) : ℤ⟦X⟧))) * hE0
  rcases mul_eq_zero.mp h0 with hg | h
  · exfalso
    have h' := congrArg (coeff 0) hg
    simp only [map_zero, coeff_term', coeff_one] at h'
    norm_num at h'
  · exact h

/-- The recurrence, read off at the coefficient of `x^(m + 3)`. -/
lemma rec_shift (m : ℕ) :
    ((1 : ℤ) * ((m : ℤ) + 3) + (1 : ℤ)) * a (m + 3) +
      ((-12 : ℤ) * ((m : ℤ) + 2) + (-15 : ℤ)) * a (m + 2) +
      ((37 : ℤ) * ((m : ℤ) + 1) + (54 : ℤ)) * a (m + 1) +
      ((-6 : ℤ) * ((m : ℤ) + 0) + (-6 : ℤ)) * a (m + 0) = 0 := by
  have hT : ((1 : ℤ) : ℤ⟦X⟧) * X ^ 1 * B +
      (((-12) : ℤ) : ℤ⟦X⟧) * X ^ 2 * B +
      ((37 : ℤ) : ℤ⟦X⟧) * X ^ 3 * B +
      (((-6) : ℤ) : ℤ⟦X⟧) * X ^ 4 * B +
      ((1 : ℤ) : ℤ⟦X⟧) * X ^ 0 * A +
      (((-15) : ℤ) : ℤ⟦X⟧) * X ^ 1 * A +
      ((54 : ℤ) : ℤ⟦X⟧) * X ^ 2 * A +
      (((-6) : ℤ) : ℤ⟦X⟧) * X ^ 3 * A +
      (((-1) : ℤ) : ℤ⟦X⟧) * X ^ 0 * (1 : ℤ⟦X⟧) +
      ((7 : ℤ) : ℤ⟦X⟧) * X ^ 1 * (1 : ℤ⟦X⟧) = 0 := by
    linear_combination (norm := (push_cast; ring)) hODE
  have h := congrArg (coeff (m + 3)) hT
  have t0 : coeff (m + 3) (((1 : ℤ) : ℤ⟦X⟧) * X ^ 1 * B) = (1 : ℤ) * (a (m + 3) * ((m : ℤ) + 3)) := by
    rw [coeff_term_B _ _ _ (by omega), show m + 3 + 1 - 1 = m + 3 by omega]; push_cast; ring
  have t1 : coeff (m + 3) ((((-12) : ℤ) : ℤ⟦X⟧) * X ^ 2 * B) = (-12 : ℤ) * (a (m + 2) * ((m : ℤ) + 2)) := by
    rw [coeff_term_B _ _ _ (by omega), show m + 3 + 1 - 2 = m + 2 by omega]; push_cast; ring
  have t2 : coeff (m + 3) (((37 : ℤ) : ℤ⟦X⟧) * X ^ 3 * B) = (37 : ℤ) * (a (m + 1) * ((m : ℤ) + 1)) := by
    rw [coeff_term_B _ _ _ (by omega), show m + 3 + 1 - 3 = m + 1 by omega]; push_cast; ring
  have t3 : coeff (m + 3) ((((-6) : ℤ) : ℤ⟦X⟧) * X ^ 4 * B) = (-6 : ℤ) * (a (m + 0) * ((m : ℤ) + 0)) := by
    rw [coeff_term_B _ _ _ (by omega), show m + 3 + 1 - 4 = m + 0 by omega]; push_cast; ring
  have t4 : coeff (m + 3) (((1 : ℤ) : ℤ⟦X⟧) * X ^ 0 * A) = (1 : ℤ) * a (m + 3) := by
    rw [coeff_term _ _ _ _ (by omega), show m + 3 - 0 = m + 3 by omega, coeff_A]
  have t5 : coeff (m + 3) ((((-15) : ℤ) : ℤ⟦X⟧) * X ^ 1 * A) = (-15 : ℤ) * a (m + 2) := by
    rw [coeff_term _ _ _ _ (by omega), show m + 3 - 1 = m + 2 by omega, coeff_A]
  have t6 : coeff (m + 3) (((54 : ℤ) : ℤ⟦X⟧) * X ^ 2 * A) = (54 : ℤ) * a (m + 1) := by
    rw [coeff_term _ _ _ _ (by omega), show m + 3 - 2 = m + 1 by omega, coeff_A]
  have t7 : coeff (m + 3) ((((-6) : ℤ) : ℤ⟦X⟧) * X ^ 3 * A) = (-6 : ℤ) * a (m + 0) := by
    rw [coeff_term _ _ _ _ (by omega), show m + 3 - 3 = m + 0 by omega, coeff_A]
  have t8 : coeff (m + 3) ((((-1) : ℤ) : ℤ⟦X⟧) * X ^ 0 * (1 : ℤ⟦X⟧)) = 0 := by
    rw [coeff_term _ _ _ _ (by omega), coeff_one, if_neg (by omega), mul_zero]
  have t9 : coeff (m + 3) (((7 : ℤ) : ℤ⟦X⟧) * X ^ 1 * (1 : ℤ⟦X⟧)) = 0 := by
    rw [coeff_term _ _ _ _ (by omega), coeff_one, if_neg (by omega), mul_zero]
  simp only [map_add, map_zero, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9] at h
  linear_combination h

end OMA.A225887

open OMA.A225887 in
theorem OMA.solution : type_of% @OMA.S_oeis_a225887.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := rec_shift m
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m + 0 by omega]
  push_cast
  linear_combination h
