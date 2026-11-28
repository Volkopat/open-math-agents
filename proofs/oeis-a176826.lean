import OMAStatements.S_oeis_a176826
import Mathlib

/-!
# OEIS A176826: Mathar's recurrence, from the algebraic generating function

The sequence is `a(0) = 1`, `a(1) = 1` and
`a(n+2) = ∑_{p ≤ n+1} (a(p) a(n+1-p) + (1)) + (-1)`.

Let `A = ∑ a(n) xⁿ`, `S = ∑ a(n+1) xⁿ` and `F = ∑ ((1)(m+1) + (-1)) x^m`. Then

* `x S = A - 1`,
* `S = A² + F + (0)` (the defining rule, coefficient by coefficient),
* `(1 - x)² F = (0) - (-1) x`,

which combine to the quadratic equation `U A² - V A + N = 0` with
`U = x (1 - x)²`, `V = (1 - x)²`, `N = 2*x**2 - 2*x + 1`.

Differentiating, and eliminating `A²`, `A³` with the quadratic itself, gives a first order
linear differential equation; after cancelling the common factor `(1 - x)^3` it reads

  `p A' + q A = r`,
  `p = 8*x**5 - 17*x**4 + 15*x**3 - 7*x**2 + x`,
  `q = 4*x**4 - 5*x**3 + 9*x**2 - 5*x + 1`,
  `r = -2*x**3 + 6*x**2 - 3*x + 1`.

Comparing the coefficients of `xⁿ` for `n ≥ 4` (beyond the degree of `r`) gives
`(n + 1) a(n-0), (2 - 7*n) a(n-1), (3*(5*n - 7)) a(n-2), (46 - 17*n) a(n-3), (4*(2*n - 7)) a(n-4) = 0`, which is the conjectured recurrence.
-/

open PowerSeries OMA.S_oeis_a176826

namespace OMA.A176826

/-- The generating function `A = ∑ a(n) xⁿ`. -/
noncomputable def A : ℤ⟦X⟧ := PowerSeries.mk a

/-- Its derivative `A'`. -/
noncomputable def B : ℤ⟦X⟧ := PowerSeries.derivative ℤ A

/-- The shifted series `S = ∑ a(n+1) xⁿ`. -/
noncomputable def S : ℤ⟦X⟧ := PowerSeries.mk fun m => a (m + 1)

/-- `F = ∑ (k (m+1) + l) x^m`. -/
noncomputable def F (k l : ℤ) : ℤ⟦X⟧ := PowerSeries.mk fun m : ℕ => k * ((m : ℤ) + 1) + l

/-! ### Coefficient bookkeeping -/

lemma coeff_intCast (c : ℤ) (n : ℕ) :
    coeff n ((c : ℤ) : ℤ⟦X⟧) = if n = 0 then c else 0 := by
  rw [← eq_intCast (C : ℤ →+* ℤ⟦X⟧) c, coeff_C]

lemma coeff_intCast_mul (c : ℤ) (φ : ℤ⟦X⟧) (n : ℕ) :
    coeff n (((c : ℤ) : ℤ⟦X⟧) * φ) = c * coeff n φ := by
  rw [← eq_intCast (C : ℤ →+* ℤ⟦X⟧) c, coeff_C_mul]

/-- The coefficient of `xⁿ` in `c xⁱ φ`. -/
lemma coeff_term (c : ℤ) (i n : ℕ) (φ : ℤ⟦X⟧) (h : i ≤ n) :
    coeff n (((c : ℤ) : ℤ⟦X⟧) * X ^ i * φ) = c * coeff (n - i) φ := by
  rw [mul_assoc, coeff_intCast_mul, coeff_X_pow_mul', if_pos h]

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

/-! ### The quadratic equation -/

lemma a_zero : a 0 = 1 := by rw [a]

lemma a_one : a 1 = 1 := by rw [a]

/-- The defining rule in terms of the coefficients of `A²`. -/
lemma a_step (m : ℕ) :
    a (m + 2) = coeff (m + 1) (A * A) + ((1 : ℤ) * ((m : ℤ) + 2) + (-1 : ℤ)) := by
  conv_lhs => rw [a]
  rw [Fin.sum_univ_eq_sum_range (fun p => a p * a (m + 1 - p) + 1) (m + 2),
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j A)]
  simp only [coeff_A]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul]
  push_cast
  ring

lemma hS : X * S = A - 1 := by
  ext n
  rcases n with _ | n
  · simp [A, a_zero]
  · simp [A, S, coeff_succ_X_mul]

lemma hrec : S = A * A + F (1) (-1) + ((0 : ℤ) : ℤ⟦X⟧) := by
  ext m
  rcases m with _ | m
  · have h1 : coeff 0 S = 1 := by simp [S, a_one]
    have h2 : coeff 0 (A * A) = 1 := by simp [A, a_zero]
    have h3 : coeff 0 (F (1) (-1)) = (1 : ℤ) + (-1 : ℤ) := by simp [F]
    rw [map_add, map_add, h1, h2, h3, coeff_intCast, if_pos rfl]
    norm_num
  · have h := a_step m
    simp only [map_add, coeff_intCast, S, F, coeff_mk, if_neg (Nat.succ_ne_zero m), add_zero]
    rw [h]
    push_cast
    ring

lemma F_eq (k l : ℤ) :
    (1 - X) * (1 - X) * F k l = ((k + l : ℤ) : ℤ⟦X⟧) - ((l : ℤ) : ℤ⟦X⟧) * X := by
  have e : (1 - X) * (1 - X) * F k l
      = F k l - (X * F k l + X * F k l) + X * (X * F k l) := by ring
  rw [e]
  ext m
  rcases m with _ | _ | m
  · simp [F]
  · simp [F, coeff_intCast, coeff_succ_X_mul]
    ring
  · simp [F, coeff_intCast, coeff_succ_X_mul]
    ring

/-- `U A² - V A + N = 0`. -/
lemma hE0 :
    X * ((1 - X) * (1 - X)) * (A * A) - (1 - X) * (1 - X) * A
      + (((1 : ℤ) : ℤ⟦X⟧) + (((-2) : ℤ) : ℤ⟦X⟧) * X + ((2 : ℤ) : ℤ⟦X⟧) * (X * X) + ((0 : ℤ) : ℤ⟦X⟧) * (X * (X * X))) = 0 := by
  linear_combination (norm := (push_cast; ring))
    ((1 - X) * (1 - X)) * hS - (X * ((1 - X) * (1 - X))) * hrec - X * F_eq (1) (-1)

/-- The derivative of the quadratic equation. -/
lemma hE1 :
    ((1 - X) * (1 - X) - 2 * X * (1 - X)) * (A * A) + 2 * (X * ((1 - X) * (1 - X))) * A * B
      - (-(2 * (1 - X))) * A - (1 - X) * (1 - X) * B
      + ((((-2) : ℤ) : ℤ⟦X⟧) + ((4 : ℤ) : ℤ⟦X⟧) * X + ((0 : ℤ) : ℤ⟦X⟧) * (X * X)) = 0 := by
  have h := congrArg (PowerSeries.derivative ℤ) hE0
  simp only [map_add, map_sub, map_zero, Derivation.leibniz, Derivation.map_intCast,
    Derivation.map_one_eq_zero, PowerSeries.derivative_X, smul_eq_mul] at h
  unfold B
  linear_combination (norm := (push_cast; ring)) h

/-! ### The differential equation -/

/-- `p A' + q A = r`. -/
lemma hODE :
    (((1 : ℤ) : ℤ⟦X⟧) * X ^ 1 + (((-7) : ℤ) : ℤ⟦X⟧) * X ^ 2 + ((15 : ℤ) : ℤ⟦X⟧) * X ^ 3 + (((-17) : ℤ) : ℤ⟦X⟧) * X ^ 4 + ((8 : ℤ) : ℤ⟦X⟧) * X ^ 5) * B
      + (((1 : ℤ) : ℤ⟦X⟧) + (((-5) : ℤ) : ℤ⟦X⟧) * X ^ 1 + ((9 : ℤ) : ℤ⟦X⟧) * X ^ 2 + (((-5) : ℤ) : ℤ⟦X⟧) * X ^ 3 + ((4 : ℤ) : ℤ⟦X⟧) * X ^ 4) * A
      - (((1 : ℤ) : ℤ⟦X⟧) + (((-3) : ℤ) : ℤ⟦X⟧) * X ^ 1 + ((6 : ℤ) : ℤ⟦X⟧) * X ^ 2 + (((-2) : ℤ) : ℤ⟦X⟧) * X ^ 3) = 0 := by
  have h0 : (1 - X) ^ 3 * ((((1 : ℤ) : ℤ⟦X⟧) * X ^ 1 + (((-7) : ℤ) : ℤ⟦X⟧) * X ^ 2 + ((15 : ℤ) : ℤ⟦X⟧) * X ^ 3 + (((-17) : ℤ) : ℤ⟦X⟧) * X ^ 4 + ((8 : ℤ) : ℤ⟦X⟧) * X ^ 5) * B
      + (((1 : ℤ) : ℤ⟦X⟧) + (((-5) : ℤ) : ℤ⟦X⟧) * X ^ 1 + ((9 : ℤ) : ℤ⟦X⟧) * X ^ 2 + (((-5) : ℤ) : ℤ⟦X⟧) * X ^ 3 + ((4 : ℤ) : ℤ⟦X⟧) * X ^ 4) * A
      - (((1 : ℤ) : ℤ⟦X⟧) + (((-3) : ℤ) : ℤ⟦X⟧) * X ^ 1 + ((6 : ℤ) : ℤ⟦X⟧) * X ^ 2 + (((-2) : ℤ) : ℤ⟦X⟧) * X ^ 3)) = 0 := by
    linear_combination (norm := (push_cast; ring))
      (X * ((1 - X) * (1 - X)) * (2 * (X * ((1 - X) * (1 - X))) * A - (1 - X) * (1 - X))) * hE1
      + (-4 * (X * ((1 - X) * (1 - X))) ^ 2 * B - 2 * (X * ((1 - X) * (1 - X))) * ((1 - X) * (1 - X) - 2 * X * (1 - X)) * A
          - ((1 - X) * (1 - X) - 2 * X * (1 - X)) * ((1 - X) * (1 - X)) + 2 * (X * ((1 - X) * (1 - X))) * (-(2 * (1 - X)))) * hE0
  rcases mul_eq_zero.mp h0 with hg | h
  · exfalso
    have hX : ((1 - X) : ℤ⟦X⟧) ≠ 0 := fun h => by
      have h' := congrArg (coeff 0) h
      simp at h'
    exact pow_ne_zero 3 hX hg
  · exact h

/-- The recurrence, read off at the coefficient of `x^(m + 4)`. -/
lemma rec_shift (m : ℕ) :
    ((1 : ℤ) * ((m : ℤ) + 4) + (1 : ℤ)) * a (m + 4) +
      ((-7 : ℤ) * ((m : ℤ) + 3) + (-5 : ℤ)) * a (m + 3) +
      ((15 : ℤ) * ((m : ℤ) + 2) + (9 : ℤ)) * a (m + 2) +
      ((-17 : ℤ) * ((m : ℤ) + 1) + (-5 : ℤ)) * a (m + 1) +
      ((8 : ℤ) * ((m : ℤ) + 0) + (4 : ℤ)) * a (m + 0) = 0 := by
  have hT : ((1 : ℤ) : ℤ⟦X⟧) * X ^ 1 * B +
      (((-7) : ℤ) : ℤ⟦X⟧) * X ^ 2 * B +
      ((15 : ℤ) : ℤ⟦X⟧) * X ^ 3 * B +
      (((-17) : ℤ) : ℤ⟦X⟧) * X ^ 4 * B +
      ((8 : ℤ) : ℤ⟦X⟧) * X ^ 5 * B +
      ((1 : ℤ) : ℤ⟦X⟧) * X ^ 0 * A +
      (((-5) : ℤ) : ℤ⟦X⟧) * X ^ 1 * A +
      ((9 : ℤ) : ℤ⟦X⟧) * X ^ 2 * A +
      (((-5) : ℤ) : ℤ⟦X⟧) * X ^ 3 * A +
      ((4 : ℤ) : ℤ⟦X⟧) * X ^ 4 * A +
      (((-1) : ℤ) : ℤ⟦X⟧) * X ^ 0 * (1 : ℤ⟦X⟧) +
      ((3 : ℤ) : ℤ⟦X⟧) * X ^ 1 * (1 : ℤ⟦X⟧) +
      (((-6) : ℤ) : ℤ⟦X⟧) * X ^ 2 * (1 : ℤ⟦X⟧) +
      ((2 : ℤ) : ℤ⟦X⟧) * X ^ 3 * (1 : ℤ⟦X⟧) = 0 := by
    linear_combination (norm := (push_cast; ring)) hODE
  have h := congrArg (coeff (m + 4)) hT
  have t0 : coeff (m + 4) (((1 : ℤ) : ℤ⟦X⟧) * X ^ 1 * B) = (1 : ℤ) * (a (m + 4) * ((m : ℤ) + 4)) := by
    rw [coeff_term_B _ _ _ (by omega), show m + 4 + 1 - 1 = m + 4 by omega]; push_cast; ring
  have t1 : coeff (m + 4) ((((-7) : ℤ) : ℤ⟦X⟧) * X ^ 2 * B) = (-7 : ℤ) * (a (m + 3) * ((m : ℤ) + 3)) := by
    rw [coeff_term_B _ _ _ (by omega), show m + 4 + 1 - 2 = m + 3 by omega]; push_cast; ring
  have t2 : coeff (m + 4) (((15 : ℤ) : ℤ⟦X⟧) * X ^ 3 * B) = (15 : ℤ) * (a (m + 2) * ((m : ℤ) + 2)) := by
    rw [coeff_term_B _ _ _ (by omega), show m + 4 + 1 - 3 = m + 2 by omega]; push_cast; ring
  have t3 : coeff (m + 4) ((((-17) : ℤ) : ℤ⟦X⟧) * X ^ 4 * B) = (-17 : ℤ) * (a (m + 1) * ((m : ℤ) + 1)) := by
    rw [coeff_term_B _ _ _ (by omega), show m + 4 + 1 - 4 = m + 1 by omega]; push_cast; ring
  have t4 : coeff (m + 4) (((8 : ℤ) : ℤ⟦X⟧) * X ^ 5 * B) = (8 : ℤ) * (a (m + 0) * ((m : ℤ) + 0)) := by
    rw [coeff_term_B _ _ _ (by omega), show m + 4 + 1 - 5 = m + 0 by omega]; push_cast; ring
  have t5 : coeff (m + 4) (((1 : ℤ) : ℤ⟦X⟧) * X ^ 0 * A) = (1 : ℤ) * a (m + 4) := by
    rw [coeff_term _ _ _ _ (by omega), show m + 4 - 0 = m + 4 by omega, coeff_A]
  have t6 : coeff (m + 4) ((((-5) : ℤ) : ℤ⟦X⟧) * X ^ 1 * A) = (-5 : ℤ) * a (m + 3) := by
    rw [coeff_term _ _ _ _ (by omega), show m + 4 - 1 = m + 3 by omega, coeff_A]
  have t7 : coeff (m + 4) (((9 : ℤ) : ℤ⟦X⟧) * X ^ 2 * A) = (9 : ℤ) * a (m + 2) := by
    rw [coeff_term _ _ _ _ (by omega), show m + 4 - 2 = m + 2 by omega, coeff_A]
  have t8 : coeff (m + 4) ((((-5) : ℤ) : ℤ⟦X⟧) * X ^ 3 * A) = (-5 : ℤ) * a (m + 1) := by
    rw [coeff_term _ _ _ _ (by omega), show m + 4 - 3 = m + 1 by omega, coeff_A]
  have t9 : coeff (m + 4) (((4 : ℤ) : ℤ⟦X⟧) * X ^ 4 * A) = (4 : ℤ) * a (m + 0) := by
    rw [coeff_term _ _ _ _ (by omega), show m + 4 - 4 = m + 0 by omega, coeff_A]
  have t10 : coeff (m + 4) ((((-1) : ℤ) : ℤ⟦X⟧) * X ^ 0 * (1 : ℤ⟦X⟧)) = 0 := by
    rw [coeff_term _ _ _ _ (by omega), coeff_one, if_neg (by omega), mul_zero]
  have t11 : coeff (m + 4) (((3 : ℤ) : ℤ⟦X⟧) * X ^ 1 * (1 : ℤ⟦X⟧)) = 0 := by
    rw [coeff_term _ _ _ _ (by omega), coeff_one, if_neg (by omega), mul_zero]
  have t12 : coeff (m + 4) ((((-6) : ℤ) : ℤ⟦X⟧) * X ^ 2 * (1 : ℤ⟦X⟧)) = 0 := by
    rw [coeff_term _ _ _ _ (by omega), coeff_one, if_neg (by omega), mul_zero]
  have t13 : coeff (m + 4) (((2 : ℤ) : ℤ⟦X⟧) * X ^ 3 * (1 : ℤ⟦X⟧)) = 0 := by
    rw [coeff_term _ _ _ _ (by omega), coeff_one, if_neg (by omega), mul_zero]
  simp only [map_add, map_zero, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13] at h
  linear_combination h

end OMA.A176826

open OMA.A176826 in
theorem OMA.solution : type_of% @OMA.S_oeis_a176826.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h := rec_shift m
  simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m + 0 by omega]
  push_cast
  linear_combination h
