import OMAStatements.S_oeis_a185965

/-! Proof. a(n) = [x^n] g^(n+1). The coefficients c(m,j) of g^m satisfy a Pascal-type rule from
(1-x+x^2) g^(m+1) = (1-x)^2 g^m and a derivative rule from (1-x)(1-x+x^2) (g^m)' = -m(1+x) g^m.
Fixed linear combinations of these rules (found by linear algebra) give both recurrences for large n;
the small cases follow from an explicit recursion for c(m,j). -/

namespace OMA.S_oeis_a185965

open PowerSeries

/-- Coefficients of powers of `g`. -/
noncomputable def c (m j : ℕ) : ℚ := coeff j (g ^ m)

lemma aC (n : ℕ) : a n = c (n + 1) n := by
  unfold a T c
  rw [mul_pow, ← mul_assoc, mul_comm g, mul_assoc, ← pow_succ', show 2 * n = n + n by ring,
    coeff_X_pow_mul']
  simp

lemma hDg : (1 - X + X ^ 2 : ℚ⟦X⟧) * g = (1 - X) ^ 2 := by
  have h : (1 - X + X ^ 2 : ℚ⟦X⟧) * (1 - X + X ^ 2)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp)
  unfold g
  calc (1 - X + X ^ 2 : ℚ⟦X⟧) * ((1 - X) ^ 2 * (1 - X + X ^ 2)⁻¹)
      = (1 - X) ^ 2 * ((1 - X + X ^ 2) * (1 - X + X ^ 2)⁻¹) := by ring
    _ = (1 - X) ^ 2 := by rw [h, mul_one]

lemma hder : (2 * X - 1 : ℚ⟦X⟧) * g + (1 - X + X ^ 2) * d⁄dX ℚ g = -2 * (1 - X) := by
  have h := congrArg (d⁄dX ℚ) hDg
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add,
    derivative_X, smul_eq_mul] at h
  simp only [Derivation.map_one_eq_zero] at h
  push_cast at h
  linear_combination h

lemma HB (m : ℕ) : (1 - X) * (1 - X + X ^ 2) * d⁄dX ℚ (g ^ m) = -((m : ℚ⟦X⟧) * (1 + X) * g ^ m) := by
  rcases m with _ | m
  · simp
  · rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
    simp only [Nat.add_sub_cancel]
    push_cast
    linear_combination ((m : ℚ⟦X⟧) + 1) * g ^ m * (1 - X) * hder + 2 * ((m : ℚ⟦X⟧) + 1) * g ^ m * hDg

lemma HA (m : ℕ) : (1 - X + X ^ 2 : ℚ⟦X⟧) * g ^ (m + 1) = (1 - X) ^ 2 * g ^ m := by
  rw [pow_succ' g m, ← mul_assoc, hDg]

lemma coeff_low (f : ℚ⟦X⟧) (j : ℕ) :
    coeff (j + 2) ((1 - X + X ^ 2 : ℚ⟦X⟧) * f) = coeff (j + 2) f - coeff (j + 1) f + coeff j f ∧
    coeff (j + 2) ((1 - X) ^ 2 * f) = coeff (j + 2) f - 2 * coeff (j + 1) f + coeff j f := by
  constructor
  · simp only [add_mul, sub_mul, one_mul, map_add, map_sub, coeff_X_pow_mul', coeff_succ_X_mul]
    simp
  · have : (1 - X) ^ 2 * f = f - X * f - X * f + X ^ 2 * f := by ring
    rw [this]
    simp only [map_add, map_sub, coeff_X_pow_mul', coeff_succ_X_mul]
    simp; ring

lemma A' (m j m1 j1 j2 : ℕ) (h1 : m1 = m + 1) (h2 : j1 = j + 1) (h3 : j2 = j + 2) :
    c m1 j2 - c m1 j1 + c m1 j = c m j2 - 2 * c m j1 + c m j := by
  subst h1 h2 h3
  have h := congrArg (coeff (j + 2)) (HA m)
  rw [(coeff_low _ j).1, (coeff_low _ j).2] at h
  unfold c
  linear_combination h

lemma B' (m j j1 j2 j3 j4 : ℕ) (h1 : j1 = j + 1) (h2 : j2 = j + 2) (h3 : j3 = j + 3)
    (h4 : j4 = j + 4) :
    ((j : ℚ) + 4) * c m j4 - 2 * ((j : ℚ) + 3) * c m j3 + 2 * ((j : ℚ) + 2) * c m j2
      - ((j : ℚ) + 1) * c m j1 = -((m : ℚ) * (c m j3 + c m j2)) := by
  subst h1 h2 h3 h4
  have h := congrArg (coeff (j + 3)) (HB m)
  have e1 : (1 - X) * (1 - X + X ^ 2) * d⁄dX ℚ (g ^ m)
      = d⁄dX ℚ (g ^ m) - X * d⁄dX ℚ (g ^ m) - X * d⁄dX ℚ (g ^ m) + X ^ 2 * d⁄dX ℚ (g ^ m)
        + X ^ 2 * d⁄dX ℚ (g ^ m) - X ^ 3 * d⁄dX ℚ (g ^ m) := by ring
  have e2 : -((m : ℚ⟦X⟧) * (1 + X) * g ^ m) = -((m : ℚ) • (g ^ m + X * g ^ m)) := by
    rw [smul_eq_C_mul]; simp; ring
  rw [e1, e2] at h
  simp only [map_add, map_sub, map_neg, map_smul, coeff_X_pow_mul', coeff_succ_X_mul,
    coeff_derivative, smul_eq_mul] at h
  simp at h
  unfold c
  ring_nf at h ⊢
  linear_combination h

/-- An explicit recursion for the coefficients `c m j`. -/
def f : ℕ → ℕ → ℤ
  | 0, j => if j = 0 then 1 else 0
  | _ + 1, 0 => 1
  | m + 1, 1 => f m 1 - 1
  | m + 1, j + 2 => f (m + 1) (j + 1) - f (m + 1) j + f m (j + 2) - 2 * f m (j + 1) + f m j

lemma c0 (m : ℕ) : c m 0 = 1 := by
  unfold c; simp [g]

lemma c1 (m : ℕ) : c (m + 1) 1 = c m 1 - 1 := by
  have h := congrArg (coeff (0 + 1)) (HA m)
  have e1 : (1 - X + X ^ 2 : ℚ⟦X⟧) * g ^ (m + 1) = g ^ (m + 1) - X * g ^ (m + 1) + X * (X * g ^ (m + 1)) := by ring
  have e2 : (1 - X : ℚ⟦X⟧) ^ 2 * g ^ m = g ^ m - X * g ^ m - X * g ^ m + X * (X * g ^ m) := by ring
  rw [e1, e2] at h
  simp only [map_add, map_sub, coeff_succ_X_mul] at h
  have h0 := c0 (m + 1)
  have h0' := c0 m
  unfold c at *
  simp only [coeff_zero_X_mul] at h
  linear_combination h + h0 - 2 * h0'

lemma cf : ∀ m j, c m j = (f m j : ℚ) := by
  intro m
  induction m with
  | zero => intro j; unfold c; rcases j with _ | j <;> simp [f, coeff_one]
  | succ m ih =>
    intro j
    induction j using Nat.strong_induction_on with
    | _ j hj =>
      match j with
      | 0 => rw [c0]; simp [f]
      | 1 => rw [c1, ih]; simp [f]
      | j + 2 =>
        have h := A' m j (m + 1) (j + 1) (j + 2) rfl rfl rfl
        rw [hj (j + 1) (by omega), hj j (by omega), ih, ih, ih] at h
        simp only [f]; push_cast
        linear_combination h

lemma aval (n : ℕ) : a n = (f (n + 1) n : ℚ) := by rw [aC, cf]

theorem solution_main :
    (∀ n : ℕ, 5 ≤ n →
      15 * (n : ℚ) * (n - 1) * a n + 10 * (2 * (n : ℚ) - 1) * (n - 1) * a (n - 1)
        + (109 * (n : ℚ) ^ 2 - 263 * n + 180) * a (n - 2)
        + 4 * (-2 * (n : ℚ) ^ 2 - 10 * n + 57) * a (n - 3)
        + 60 * ((n : ℚ) - 4) ^ 2 * a (n - 4) - 6 * (2 * (n : ℚ) - 7) * (n - 5) * a (n - 5) = 0) ∧
    (∀ n : ℕ, 4 ≤ n →
      3 * (n : ℚ) * (n - 1) * (57 * n - 136) * a n
        + ((n : ℚ) - 1) * (171 * n ^ 2 - 415 * n + 14) * a (n - 1)
        + 2 * (532 * (n : ℚ) ^ 3 - 2281 * n ^ 2 + 2755 * n - 840) * a (n - 2)
        - 2 * ((n : ℚ) - 3) * (304 * n ^ 2 - 835 * n + 216) * a (n - 3)
        + 2 * (19 * (n : ℚ) - 5) * (n - 4) * (2 * n - 5) * a (n - 4) = 0) := by
  have v0 : f 1 0 = 1 := by simp [f]
  have v1 : f 2 1 = -2 := by simp [f]
  have v2 : f 3 2 = 0 := by simp [f]
  have v3 : f 4 3 = 8 := by simp [f]
  have v4 : f 5 4 = -10 := by simp [f]
  have v5 : f 6 5 = -30 := by simp [f]
  have v6 : f 7 6 = 98 := by simp [f]
  constructor
  · intro n hn
    rcases (show n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | h7
    · norm_num [aval, v0, v1, v2, v3, v4, v5]
    · norm_num [aval, v0, v1, v2, v3, v4, v5, v6]
    · obtain ⟨M, rfl⟩ : ∃ M, n = M + 7 := ⟨n - 7, by omega⟩
      rw [show M + 7 - 1 = M + 6 by omega, show M + 7 - 2 = M + 5 by omega,
        show M + 7 - 3 = M + 4 by omega, show M + 7 - 4 = M + 3 by omega,
        show M + 7 - 5 = M + 2 by omega]
      have q0 : a (M + 7) = c (M + 8) (M + 7) := aC _
      have q1 : a (M + 6) = c (M + 7) (M + 6) := aC _
      have q2 : a (M + 5) = c (M + 6) (M + 5) := aC _
      have q3 : a (M + 4) = c (M + 5) (M + 4) := aC _
      have q4 : a (M + 3) = c (M + 4) (M + 3) := aC _
      have q5 : a (M + 2) = c (M + 3) (M + 2) := aC _
      rw [q0, q1, q2, q3, q4, q5]
      have hne : ((M : ℚ) + 4) * ((M : ℚ) + 5) ≠ 0 := by positivity
      rw [← mul_right_inj' hne, mul_zero]
      have h0 := B' (M+3) (M+0) (M+1) (M+2) (M+3) (M+4) (by ring) (by ring) (by ring) (by ring)
      have h1 := B' (M+3) (M+1) (M+2) (M+3) (M+4) (M+5) (by ring) (by ring) (by ring) (by ring)
      have h2 := B' (M+4) (M+0) (M+1) (M+2) (M+3) (M+4) (by ring) (by ring) (by ring) (by ring)
      have h3 := B' (M+4) (M+1) (M+2) (M+3) (M+4) (M+5) (by ring) (by ring) (by ring) (by ring)
      have h4 := B' (M+5) (M+0) (M+1) (M+2) (M+3) (M+4) (by ring) (by ring) (by ring) (by ring)
      have h5 := B' (M+5) (M+1) (M+2) (M+3) (M+4) (M+5) (by ring) (by ring) (by ring) (by ring)
      have h6 := B' (M+6) (M+0) (M+1) (M+2) (M+3) (M+4) (by ring) (by ring) (by ring) (by ring)
      have h7 := B' (M+6) (M+1) (M+2) (M+3) (M+4) (M+5) (by ring) (by ring) (by ring) (by ring)
      have h8 := B' (M+7) (M+0) (M+1) (M+2) (M+3) (M+4) (by ring) (by ring) (by ring) (by ring)
      have h9 := B' (M+7) (M+1) (M+2) (M+3) (M+4) (M+5) (by ring) (by ring) (by ring) (by ring)
      have h10 := B' (M+7) (M+2) (M+3) (M+4) (M+5) (M+6) (by ring) (by ring) (by ring) (by ring)
      have h11 := B' (M+8) (M+0) (M+1) (M+2) (M+3) (M+4) (by ring) (by ring) (by ring) (by ring)
      have h12 := B' (M+8) (M+1) (M+2) (M+3) (M+4) (M+5) (by ring) (by ring) (by ring) (by ring)
      have h13 := B' (M+8) (M+2) (M+3) (M+4) (M+5) (M+6) (by ring) (by ring) (by ring) (by ring)
      have h14 := B' (M+8) (M+3) (M+4) (M+5) (M+6) (M+7) (by ring) (by ring) (by ring) (by ring)
      have h15 := A' (M+3) (M+1) (M+4) (M+2) (M+3) (by ring) (by ring) (by ring)
      have h16 := A' (M+3) (M+2) (M+4) (M+3) (M+4) (by ring) (by ring) (by ring)
      have h17 := A' (M+3) (M+3) (M+4) (M+4) (M+5) (by ring) (by ring) (by ring)
      have h18 := A' (M+4) (M+1) (M+5) (M+2) (M+3) (by ring) (by ring) (by ring)
      have h19 := A' (M+4) (M+2) (M+5) (M+3) (M+4) (by ring) (by ring) (by ring)
      have h20 := A' (M+4) (M+3) (M+5) (M+4) (M+5) (by ring) (by ring) (by ring)
      have h21 := A' (M+5) (M+1) (M+6) (M+2) (M+3) (by ring) (by ring) (by ring)
      have h22 := A' (M+5) (M+2) (M+6) (M+3) (M+4) (by ring) (by ring) (by ring)
      have h23 := A' (M+5) (M+3) (M+6) (M+4) (M+5) (by ring) (by ring) (by ring)
      have h24 := A' (M+6) (M+1) (M+7) (M+2) (M+3) (by ring) (by ring) (by ring)
      have h25 := A' (M+6) (M+2) (M+7) (M+3) (M+4) (by ring) (by ring) (by ring)
      have h26 := A' (M+6) (M+3) (M+7) (M+4) (M+5) (by ring) (by ring) (by ring)
      have h27 := A' (M+7) (M+1) (M+8) (M+2) (M+3) (by ring) (by ring) (by ring)
      have h28 := A' (M+7) (M+2) (M+8) (M+3) (M+4) (by ring) (by ring) (by ring)
      have h29 := A' (M+7) (M+3) (M+8) (M+4) (M+5) (by ring) (by ring) (by ring)
      push_cast at *
      linear_combination (-6*((M:ℚ) + 2)*((M:ℚ) + 5)*(2*(M:ℚ) + 7)) * h0 + (6*((M:ℚ) + 2)*((M:ℚ) + 3)*((M:ℚ) + 5)) * h1 + (3*(7*(M:ℚ)^3 + 79*(M:ℚ)^2 + 282*(M:ℚ) + 320)) * h2 + (3*((M:ℚ) + 3)*((M:ℚ)^2 + 8*(M:ℚ) + 20)) * h3 + (-3*(M:ℚ)^3 - 35*(M:ℚ)^2 - 114*(M:ℚ) - 100) * h4 + (-((M:ℚ) + 4)*(13*(M:ℚ)^2 + 135*(M:ℚ) + 320)) * h5 + (-((M:ℚ) + 4)*((M:ℚ) + 5)*(61*(M:ℚ) + 342)) * h6 + (2*((M:ℚ) + 4)*(54*(M:ℚ)^2 + 583*(M:ℚ) + 1550)) * h7 + (20*((M:ℚ) + 4)*((M:ℚ) + 5)*((M:ℚ) + 7)) * h8 + (20*((M:ℚ) + 3)*((M:ℚ) + 4)*((M:ℚ) + 5)) * h9 + (10*((M:ℚ) + 4)*((M:ℚ) + 5)*(2*(M:ℚ) + 13)) * h10 + (5*((M:ℚ) + 4)*((M:ℚ) + 5)*(7*(M:ℚ) + 36)) * h11 + (-5*((M:ℚ) + 4)*((M:ℚ) + 5)*(5*(M:ℚ) + 24)) * h12 + (15*((M:ℚ) + 4)^2*((M:ℚ) + 5)) * h13 + (15*((M:ℚ) + 4)*((M:ℚ) + 5)*((M:ℚ) + 6)) * h14 + (6*((M:ℚ) + 1)*((M:ℚ) + 2)*((M:ℚ) + 5)*(2*(M:ℚ) + 7)) * h15 + (-6*((M:ℚ) + 2)*((M:ℚ) + 5)*((M:ℚ)^2 + 7*(M:ℚ) + 13)) * h16 + (6*((M:ℚ) + 2)*((M:ℚ) + 3)*((M:ℚ) + 5)^2) * h17 + (-3*((M:ℚ) + 1)*((M:ℚ) + 3)*((M:ℚ) + 6)*(3*(M:ℚ) + 10)) * h18 + (6*((M:ℚ) + 3)*((M:ℚ) + 4)*(4*(M:ℚ)^2 + 35*(M:ℚ) + 70)) * h19 + (3*((M:ℚ) + 3)*((M:ℚ) + 4)*((M:ℚ) + 5)*(3*(M:ℚ) + 10)) * h20 + (-2*((M:ℚ) + 1)*((M:ℚ) + 4)*((M:ℚ) + 5)*(3*(M:ℚ) + 11)) * h21 + (5*((M:ℚ) + 3)*((M:ℚ) + 4)*(5*(M:ℚ)^2 + 48*(M:ℚ) + 106)) * h22 + (-2*((M:ℚ) + 4)*((M:ℚ) + 5)*(2*(M:ℚ)^2 + 39*(M:ℚ) + 115)) * h23 + (5*((M:ℚ) + 1)*((M:ℚ) + 4)*((M:ℚ) + 5)*(11*(M:ℚ) + 64)) * h24 + (-10*((M:ℚ) + 4)*((M:ℚ) + 5)*(15*(M:ℚ)^2 + 151*(M:ℚ) + 368)) * h25 + (-5*((M:ℚ) + 4)*((M:ℚ) + 5)*((M:ℚ)^2 + 35*(M:ℚ) + 162)) * h26 + (5*((M:ℚ) + 1)*((M:ℚ) + 4)*((M:ℚ) + 5)*(7*(M:ℚ) + 36)) * h27 + (-5*((M:ℚ) + 4)*((M:ℚ) + 5)*(19*(M:ℚ)^2 + 183*(M:ℚ) + 444)) * h28 + (-5*((M:ℚ) + 4)*((M:ℚ) + 5)^2*((M:ℚ) + 36)) * h29

  · intro n hn
    rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | h6
    · norm_num [aval, v0, v1, v2, v3, v4]
    · norm_num [aval, v0, v1, v2, v3, v4, v5]
    · obtain ⟨M, rfl⟩ : ∃ M, n = M + 6 := ⟨n - 6, by omega⟩
      rw [show M + 6 - 1 = M + 5 by omega, show M + 6 - 2 = M + 4 by omega,
        show M + 6 - 3 = M + 3 by omega, show M + 6 - 4 = M + 2 by omega]
      have q0 : a (M + 6) = c (M + 7) (M + 6) := aC _
      have q1 : a (M + 5) = c (M + 6) (M + 5) := aC _
      have q2 : a (M + 4) = c (M + 5) (M + 4) := aC _
      have q3 : a (M + 3) = c (M + 4) (M + 3) := aC _
      have q4 : a (M + 2) = c (M + 3) (M + 2) := aC _
      rw [q0, q1, q2, q3, q4]
      have hne : ((M : ℚ) + 4) ≠ 0 := by positivity
      rw [← mul_right_inj' hne, mul_zero]
      have h0 := B' (M+3) (M+0) (M+1) (M+2) (M+3) (M+4) (by ring) (by ring) (by ring) (by ring)
      have h1 := B' (M+3) (M+1) (M+2) (M+3) (M+4) (M+5) (by ring) (by ring) (by ring) (by ring)
      have h2 := B' (M+4) (M+0) (M+1) (M+2) (M+3) (M+4) (by ring) (by ring) (by ring) (by ring)
      have h3 := B' (M+4) (M+1) (M+2) (M+3) (M+4) (M+5) (by ring) (by ring) (by ring) (by ring)
      have h4 := B' (M+5) (M+0) (M+1) (M+2) (M+3) (M+4) (by ring) (by ring) (by ring) (by ring)
      have h5 := B' (M+5) (M+1) (M+2) (M+3) (M+4) (M+5) (by ring) (by ring) (by ring) (by ring)
      have h6 := B' (M+6) (M+0) (M+1) (M+2) (M+3) (M+4) (by ring) (by ring) (by ring) (by ring)
      have h7 := B' (M+6) (M+1) (M+2) (M+3) (M+4) (M+5) (by ring) (by ring) (by ring) (by ring)
      have h8 := B' (M+7) (M+0) (M+1) (M+2) (M+3) (M+4) (by ring) (by ring) (by ring) (by ring)
      have h9 := B' (M+7) (M+1) (M+2) (M+3) (M+4) (M+5) (by ring) (by ring) (by ring) (by ring)
      have h10 := B' (M+7) (M+2) (M+3) (M+4) (M+5) (M+6) (by ring) (by ring) (by ring) (by ring)
      have h11 := A' (M+3) (M+1) (M+4) (M+2) (M+3) (by ring) (by ring) (by ring)
      have h12 := A' (M+3) (M+2) (M+4) (M+3) (M+4) (by ring) (by ring) (by ring)
      have h13 := A' (M+3) (M+3) (M+4) (M+4) (M+5) (by ring) (by ring) (by ring)
      have h14 := A' (M+4) (M+1) (M+5) (M+2) (M+3) (by ring) (by ring) (by ring)
      have h15 := A' (M+4) (M+2) (M+5) (M+3) (M+4) (by ring) (by ring) (by ring)
      have h16 := A' (M+4) (M+3) (M+5) (M+4) (M+5) (by ring) (by ring) (by ring)
      have h17 := A' (M+5) (M+1) (M+6) (M+2) (M+3) (by ring) (by ring) (by ring)
      have h18 := A' (M+5) (M+2) (M+6) (M+3) (M+4) (by ring) (by ring) (by ring)
      have h19 := A' (M+5) (M+3) (M+6) (M+4) (M+5) (by ring) (by ring) (by ring)
      have h20 := A' (M+6) (M+1) (M+7) (M+2) (M+3) (by ring) (by ring) (by ring)
      have h21 := A' (M+6) (M+2) (M+7) (M+3) (M+4) (by ring) (by ring) (by ring)
      have h22 := A' (M+6) (M+3) (M+7) (M+4) (M+5) (by ring) (by ring) (by ring)
      push_cast at *
      linear_combination (2*((M:ℚ) + 2)*(2*(M:ℚ) + 7)*(19*(M:ℚ) + 109)) * h0 + (-2*((M:ℚ) + 2)*((M:ℚ) + 3)*(19*(M:ℚ) + 109)) * h1 + (-247*(M:ℚ)^3 - 2923*(M:ℚ)^2 - 10954*(M:ℚ) - 13120) * h2 + (-((M:ℚ) + 3)*(19*(M:ℚ)^2 + 280*(M:ℚ) + 948)) * h3 + (-2*(19*(M:ℚ)^3 + 210*(M:ℚ)^2 + 917*(M:ℚ) + 1458)) * h4 + (2*((M:ℚ) + 4)*(323*(M:ℚ)^2 + 2755*(M:ℚ) + 5694)) * h5 + (((M:ℚ) + 4)*(95*(M:ℚ)^2 + 671*(M:ℚ) + 1186)) * h6 + (-((M:ℚ) + 4)*(19*(M:ℚ)^2 + 261*(M:ℚ) + 696)) * h7 + (2*((M:ℚ) + 4)*((M:ℚ) + 5)*(57*(M:ℚ) + 206)) * h8 + (-4*((M:ℚ) + 4)*((M:ℚ) + 5)*(57*(M:ℚ) + 206)) * h9 + (3*((M:ℚ) + 4)*((M:ℚ) + 5)*(57*(M:ℚ) + 206)) * h10 + (-2*((M:ℚ) + 1)*((M:ℚ) + 2)*(2*(M:ℚ) + 7)*(19*(M:ℚ) + 109)) * h11 + (2*((M:ℚ) + 2)*(19*(M:ℚ) + 109)*((M:ℚ)^2 + 7*(M:ℚ) + 13)) * h12 + (-2*((M:ℚ) + 2)*((M:ℚ) + 3)*((M:ℚ) + 5)*(19*(M:ℚ) + 109)) * h13 + (((M:ℚ) + 1)*((M:ℚ) + 3)*(171*(M:ℚ)^2 + 1556*(M:ℚ) + 3356)) * h14 + (-2*((M:ℚ) + 3)*((M:ℚ) + 4)*(133*(M:ℚ)^2 + 1269*(M:ℚ) + 2934)) * h15 + (-((M:ℚ) + 3)*((M:ℚ) + 4)*((M:ℚ) + 5)*(57*(M:ℚ) + 346)) * h16 + (((M:ℚ) + 1)*((M:ℚ) + 4)*(209*(M:ℚ)^2 + 1653*(M:ℚ) + 3246)) * h17 + (-((M:ℚ) + 3)*((M:ℚ) + 4)*(779*(M:ℚ)^2 + 6779*(M:ℚ) + 14322)) * h18 + (((M:ℚ) + 4)*((M:ℚ) + 5)*(589*(M:ℚ)^2 + 4993*(M:ℚ) + 10350)) * h19 + (2*((M:ℚ) + 1)*((M:ℚ) + 4)*((M:ℚ) + 5)*(57*(M:ℚ) + 206)) * h20 + (-4*((M:ℚ) + 4)*((M:ℚ) + 5)*(2*(M:ℚ) + 7)*(57*(M:ℚ) + 206)) * h21 + (((M:ℚ) + 4)*((M:ℚ) + 5)*(7*(M:ℚ) + 29)*(57*(M:ℚ) + 206)) * h22

end OMA.S_oeis_a185965

theorem OMA.solution : type_of% @OMA.S_oeis_a185965.main := OMA.S_oeis_a185965.solution_main
