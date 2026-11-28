import OMAStatements.S_oeis_a045994

namespace OMA.S_oeis_a045994

open PowerSeries



lemma M_rec (n : ℕ) : M (n + 2) = M (n + 1) + ∑ k ∈ Finset.range (n + 1), M k * M (n - k) := by
  rw [M, Fin.sum_univ_eq_sum_range (fun k => M k * M (n - k)) (n + 1)]

/-- The Motzkin g.f. -/
noncomputable def Ms : ℤ⟦X⟧ := PowerSeries.mk fun n => M n

/-- The g.f. A(x) = Sum a(n) x^n. -/
noncomputable def A : ℤ⟦X⟧ := PowerSeries.mk fun n => a n

lemma coeff_Ms (n : ℕ) : coeff n Ms = M n := by simp [Ms]

lemma coeff_A (n : ℕ) : coeff n A = a n := by simp [A]

lemma coeff_Ms_sq (n : ℕ) :
    coeff n (Ms ^ 2) = ∑ k ∈ Finset.range (n + 1), M k * M (n - k) := by
  rw [sq, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i Ms * coeff j Ms)]
  simp only [coeff_Ms]

lemma coeff_Ms_A (n : ℕ) :
    coeff n (Ms * A) = ∑ k ∈ Finset.range (n + 1), M k * a (n - k) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i Ms * coeff j A)]
  simp only [coeff_Ms, coeff_A]

/-- The Motzkin quadratic x^2 M^2 + (x - 1) M + 1 = 0. -/
lemma hQM : X ^ 2 * Ms ^ 2 + (X - 1) * Ms + 1 = 0 := by
  have e : X ^ 2 * Ms ^ 2 + (X - 1) * Ms + 1 = Ms ^ 2 * X ^ 2 + Ms * X ^ 1 - Ms + 1 := by ring
  rw [e]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_one, coeff_Ms, map_zero]
  rcases n with _ | _ | n
  · simp [M]
  · simp [M]
  · rw [M_rec, ← coeff_Ms_sq]
    simp only [show 2 ≤ n + 2 by omega, show 1 ≤ n + 2 by omega, if_true,
      show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega, show n + 2 ≠ 0 by omega,
      if_false]
    ring

lemma sum_Icc (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, M k * a (n - k) =
      ∑ k ∈ Finset.range (n + 1), M k * a (n - k) - a n := by
  rw [Finset.sum_range_succ', ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [show n + 1 - 1 = n by omega, Nat.sub_zero]
  rw [show M 0 = 1 by simp [M]]
  simp only [one_mul, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_comm 1 k]

/-- The definition as a g.f. identity: A = M + x (M - 1) A. -/
lemma hA : A = Ms + X * ((Ms - 1) * A) := by
  ext n
  rcases n with _ | n
  · rw [map_add, coeff_zero_X_mul, add_zero, coeff_A, coeff_Ms]
    simp [a, M]
  · rw [map_add, coeff_succ_X_mul, sub_mul, one_mul, map_sub, coeff_Ms_A, coeff_A, coeff_A,
      coeff_Ms, a, sum_Icc]

/-- The quadratic equation alpha A^2 + beta A + 1 = 0. -/
lemma quad : (X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 - X) * A ^ 2 + (X ^ 2 + 2 * X - 1) * A + 1 = 0 := by
  have hRel : Ms * (1 + X * A) - A * (1 + X) = 0 := by
    have h := hA
    linear_combination -h
  linear_combination (1 + X * A) ^ 2 * hQM -
    (X ^ 2 * (Ms * (1 + X * A) + A * (1 + X)) + (X - 1) * (1 + X * A)) * hRel

@[simp] lemma d_ofNat (n : ℕ) [n.AtLeastTwo] :
    d⁄dX ℤ (no_index (OfNat.ofNat n : ℤ⟦X⟧)) = 0 :=
  Derivation.map_natCast _ n

/-- The derivative of the quadratic equation. -/
lemma dquad : (4 * X ^ 3 + 9 * X ^ 2 + 4 * X - 1) * A ^ 2 +
    (2 * (X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 - X) * A + (X ^ 2 + 2 * X - 1)) * d⁄dX ℤ A +
    (2 * X + 2) * A = 0 := by
  have e : (4 * X ^ 3 + 9 * X ^ 2 + 4 * X - 1) * A ^ 2 +
      (2 * (X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 - X) * A + (X ^ 2 + 2 * X - 1)) * d⁄dX ℤ A +
      (2 * X + 2) * A =
      d⁄dX ℤ ((X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 - X) * A ^ 2 + (X ^ 2 + 2 * X - 1) * A + 1) := by
    simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow,
      derivative_X, Derivation.map_one_eq_zero, d_ofNat, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [e, quad, map_zero]

/-- Mathar's recurrence as a differential equation: x C A' + D A = B. -/
lemma ode : X * (1 - 4 * X - 2 * X ^ 2 + 11 * X ^ 3 + 11 * X ^ 4 + 3 * X ^ 5) * d⁄dX ℤ A +
    (1 - 6 * X + 2 * X ^ 2 + 14 * X ^ 3 + 17 * X ^ 4 + 6 * X ^ 5) * A = 1 - 4 * X + X ^ 2 := by
  have key : (2 * (X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 - X) * A + (X ^ 2 + 2 * X - 1)) *
      ((1 - 4 * X + X ^ 2) - (1 - 6 * X + 2 * X ^ 2 + 14 * X ^ 3 + 17 * X ^ 4 + 6 * X ^ 5) * A -
        X * (1 - 4 * X - 2 * X ^ 2 + 11 * X ^ 3 + 11 * X ^ 4 + 3 * X ^ 5) * d⁄dX ℤ A) = 0 := by
    linear_combination (-1 + 6 * X - 8 * X ^ 2 - 2 * X ^ 3 + X ^ 4) * quad -
      X * (1 - 4 * X - 2 * X ^ 2 + 11 * X ^ 3 + 11 * X ^ 4 + 3 * X ^ 5) * dquad
  have hne : (2 * (X ^ 4 + 3 * X ^ 3 + 2 * X ^ 2 - X) * A + (X ^ 2 + 2 * X - 1) : ℤ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  have h := (mul_eq_zero.mp key).resolve_left hne
  linear_combination -h

lemma coeff_T (n : ℕ) : coeff n (X * d⁄dX ℤ A) = (n : ℤ) * a n := by
  rcases n with _ | n
  · simp
  · rw [mul_comm, coeff_succ_mul_X, coeff_derivative, coeff_A]
    push_cast
    ring

/-- Mathar's recurrence for n >= 5. -/
theorem recurrence : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 1) * a n + 2 * (-2 * (n : ℤ) - 1) * a (n - 1) + 2 * (-(n : ℤ) + 3) * a (n - 2) +
      (11 * (n : ℤ) - 19) * a (n - 3) + (11 * (n : ℤ) - 27) * a (n - 4) +
      3 * ((n : ℤ) - 3) * a (n - 5) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e : X * (1 - 4 * X - 2 * X ^ 2 + 11 * X ^ 3 + 11 * X ^ 4 + 3 * X ^ 5) * d⁄dX ℤ A +
      (1 - 6 * X + 2 * X ^ 2 + 14 * X ^ 3 + 17 * X ^ 4 + 6 * X ^ 5) * A =
      X * d⁄dX ℤ A - C (4 : ℤ) * (X * d⁄dX ℤ A * X ^ 1) - C (2 : ℤ) * (X * d⁄dX ℤ A * X ^ 2) +
        C (11 : ℤ) * (X * d⁄dX ℤ A * X ^ 3) + C (11 : ℤ) * (X * d⁄dX ℤ A * X ^ 4) +
        C (3 : ℤ) * (X * d⁄dX ℤ A * X ^ 5) + (A - C (6 : ℤ) * (A * X ^ 1) +
        C (2 : ℤ) * (A * X ^ 2) + C (14 : ℤ) * (A * X ^ 3) + C (17 : ℤ) * (A * X ^ 4) +
        C (6 : ℤ) * (A * X ^ 5)) := by
    simp only [map_ofNat]
    ring
  have eB : (1 - 4 * X + X ^ 2 : ℤ⟦X⟧) = 1 - C (4 : ℤ) * X ^ 1 + X ^ 2 := by
    simp only [map_ofNat]
    ring
  have h := congrArg (coeff (m + 5)) ode
  rw [e, eB] at h
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_X_pow,
    coeff_one, coeff_A, coeff_T, show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega,
    show 3 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, show 5 ≤ m + 5 by omega, if_true,
    show m + 5 ≠ 0 by omega, show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, if_false,
    show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    show m + 5 - 5 = m by omega, show m + 4 ≠ 0 by omega] at h
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    show m + 5 - 5 = m by omega]
  push_cast at h ⊢
  linear_combination h

/-- Controls: M(0..5) = 1, 1, 2, 4, 9, 21 and a(0..5) = 1, 1, 3, 7, 18, 47 as in the entry. -/
lemma controls : M 2 = 2 ∧ M 3 = 4 ∧ M 4 = 9 ∧ M 5 = 21 ∧
    a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 7 ∧ a 4 = 18 ∧ a 5 = 47 := by
  decide +kernel

end OMA.S_oeis_a045994

theorem OMA.solution : type_of% @OMA.S_oeis_a045994.main :=
  OMA.S_oeis_a045994.recurrence
