import OMAStatements.S_oeis_a177203

namespace OMA.S_oeis_a177203

open PowerSeries


lemma a_zero : a 0 = 1 := by rw [a]

lemma a_one : a 1 = 10 := by rw [a]

lemma a_rec (n : ℕ) :
    a (n + 2) = (∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p)) + ((-1) * ((n : ℤ) + 2) + 1) := by
  rw [a, Fin.sum_univ_eq_sum_range (fun p => (a p * a (n + 1 - p) - 1)) (n + 2)]
  try simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  ring

/-- The g.f. A(x) = Sum a(n) x^n in Z[[x]]. -/
noncomputable def A : ℤ⟦X⟧ := PowerSeries.mk fun n => a n

lemma coeff_A (n : ℕ) : coeff n A = a n := by simp [A]

lemma coeff_A_sq (n : ℕ) :
    coeff n (A ^ 2) = ∑ p ∈ Finset.range (n + 1), a p * a (n - p) := by
  rw [sq, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j A)]
  simp only [coeff_A]

/-- a(m+2) = [x^(m+1)] A^2 + k (m + 2) + l. -/
lemma hr (m : ℕ) : a (m + 2) = coeff (m + 1) (A ^ 2) + ((-1) * ((m : ℤ) + 2) + 1) := by
  rw [a_rec, coeff_A_sq]

lemma c_zero : coeff 0 (A ^ 2) = 1 := by
  rw [coeff_A_sq]; simp [a_zero]

lemma c_one : coeff 1 (A ^ 2) = 20 := by
  rw [coeff_A_sq]; simp [Finset.sum_range_succ, a_zero, a_one]

lemma a_two : a 2 = 19 := by
  have h := hr 0
  rw [c_one] at h
  simp at h
  linarith

lemma c_two : coeff 2 (A ^ 2) = 138 := by
  rw [coeff_A_sq]; simp [Finset.sum_range_succ, a_zero, a_one, a_two]

lemma a_three : a 3 = 136 := by
  have h := hr 1
  rw [c_two] at h
  simp at h
  linarith

/-- The quadratic equation alpha A^2 + beta A + gamma = 0, expanded. -/
lemma quad : (X - 2 * X ^ 2 + X ^ 3) * A ^ 2 + (2 * X - 1 - X ^ 2) * A +
    (1 + 7 * X - 18 * X ^ 2 + 9 * X ^ 3) = 0 := by
  have e : (X - 2 * X ^ 2 + X ^ 3) * A ^ 2 + (2 * X - 1 - X ^ 2) * A +
      (1 + 7 * X - 18 * X ^ 2 + 9 * X ^ 3) =
      A ^ 2 * X ^ 1 - C (2 : ℤ) * (A ^ 2 * X ^ 2) + A ^ 2 * X ^ 3 + C (2 : ℤ) * (A * X ^ 1) - A -
        A * X ^ 2 + (1 + C (7 : ℤ) * X ^ 1 - C (18 : ℤ) * X ^ 2 + C (9 : ℤ) * X ^ 3) := by
    rw [show (C (2 : ℤ) : ℤ⟦X⟧) = 2 from map_ofNat C 2,
      show (C (7 : ℤ) : ℤ⟦X⟧) = 7 from map_ofNat C 7,
      show (C (9 : ℤ) : ℤ⟦X⟧) = 9 from map_ofNat C 9,
      show (C (18 : ℤ) : ℤ⟦X⟧) = 18 from map_ofNat C 18]
    ring
  rw [e]
  ext n
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_X_pow,
    coeff_one, coeff_A, map_zero]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num [c_zero, c_one, c_two, a_zero, a_one, a_two, a_three]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h4 := hr (m + 2)
    have h3 := hr (m + 1)
    have h2 := hr m
    rw [show m + 2 + 2 = m + 4 by omega, show m + 2 + 1 = m + 3 by omega] at h4
    rw [show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at h3
    simp only [show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega,
      if_true, show m + 4 ≠ 0 by omega, show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega,
      show m + 4 ≠ 3 by omega, if_false, show m + 4 - 1 = m + 3 by omega,
      show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega,
      show m + 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega]
    push_cast at h4 h3 h2
    linarith

@[simp] lemma d_ofNat (n : ℕ) [n.AtLeastTwo] :
    d⁄dX ℤ (no_index (OfNat.ofNat n : ℤ⟦X⟧)) = 0 :=
  Derivation.map_natCast _ n

/-- The derivative of the quadratic equation. -/
lemma dquad : (1 - 4 * X + 3 * X ^ 2) * A ^ 2 +
    (2 * (X - 2 * X ^ 2 + X ^ 3) * A + (2 * X - 1 - X ^ 2)) * d⁄dX ℤ A +
    (2 - 2 * X) * A + (7 - 36 * X + 27 * X ^ 2) = 0 := by
  have e : (1 - 4 * X + 3 * X ^ 2) * A ^ 2 +
      (2 * (X - 2 * X ^ 2 + X ^ 3) * A + (2 * X - 1 - X ^ 2)) * d⁄dX ℤ A +
      (2 - 2 * X) * A + (7 - 36 * X + 27 * X ^ 2) =
      d⁄dX ℤ ((X - 2 * X ^ 2 + X ^ 3) * A ^ 2 + (2 * X - 1 - X ^ 2) * A +
        (1 + 7 * X - 18 * X ^ 2 + 9 * X ^ 3)) := by
    simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow,
      derivative_X, Derivation.map_one_eq_zero, d_ofNat, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [e, quad, map_zero]

/-- Mathar's recurrence as a differential equation: x C A' + D A = B. -/
lemma ode : X * (1 - 7 * X - 21 * X ^ 2 + 99 * X ^ 3 - 108 * X ^ 4 + 36 * X ^ 5) * d⁄dX ℤ A + (1 - 5 * X + 9 * X ^ 2 - 9 * X ^ 3) * A = 1 + 15 * X - 54 * X ^ 2 + 54 * X ^ 3 - 18 * X ^ 4 := by
  have key : (2 * (X - 2 * X ^ 2 + X ^ 3) * A + (2 * X - 1 - X ^ 2)) *
      ((1 + 15 * X - 54 * X ^ 2 + 54 * X ^ 3 - 18 * X ^ 4) - (1 - 5 * X + 9 * X ^ 2 - 9 * X ^ 3) * A - X * (1 - 7 * X - 21 * X ^ 2 + 99 * X ^ 3 - 108 * X ^ 4 + 36 * X ^ 5) * d⁄dX ℤ A) = 0 := by
    linear_combination (-1 + X - 27 * X ^ 2 + 171 * X ^ 3 - 252 * X ^ 4 + 108 * X ^ 5) * quad - X * (1 - 7 * X - 21 * X ^ 2 + 99 * X ^ 3 - 108 * X ^ 4 + 36 * X ^ 5) * dquad
  have hne : (2 * (X - 2 * X ^ 2 + X ^ 3) * A + (2 * X - 1 - X ^ 2) : ℤ⟦X⟧) ≠ 0 := by
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
    ((n : ℤ) + 1) * a n +
      (2 - 7 * (n : ℤ)) * a (n - 1) +
      3 * (17 - 7 * (n : ℤ)) * a (n - 2) +
      9 * (11 * (n : ℤ) - 34) * a (n - 3) +
      108 * (4 - (n : ℤ)) * a (n - 4) +
      36 * ((n : ℤ) - 5) * a (n - 5) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e : X * (1 - 7 * X - 21 * X ^ 2 + 99 * X ^ 3 - 108 * X ^ 4 + 36 * X ^ 5) * d⁄dX ℤ A + (1 - 5 * X + 9 * X ^ 2 - 9 * X ^ 3) * A =
      X * d⁄dX ℤ A - C (7 : ℤ) * (X * d⁄dX ℤ A * X ^ 1) - C (21 : ℤ) * (X * d⁄dX ℤ A * X ^ 2) + C (99 : ℤ) * (X * d⁄dX ℤ A * X ^ 3) - C (108 : ℤ) * (X * d⁄dX ℤ A * X ^ 4) + C (36 : ℤ) * (X * d⁄dX ℤ A * X ^ 5) + (A - C (5 : ℤ) * (A * X ^ 1) + C (9 : ℤ) * (A * X ^ 2) - C (9 : ℤ) * (A * X ^ 3)) := by
    rw [show (C (5 : ℤ) : ℤ⟦X⟧) = 5 from map_ofNat C 5,
      show (C (7 : ℤ) : ℤ⟦X⟧) = 7 from map_ofNat C 7,
      show (C (9 : ℤ) : ℤ⟦X⟧) = 9 from map_ofNat C 9,
      show (C (21 : ℤ) : ℤ⟦X⟧) = 21 from map_ofNat C 21,
      show (C (36 : ℤ) : ℤ⟦X⟧) = 36 from map_ofNat C 36,
      show (C (99 : ℤ) : ℤ⟦X⟧) = 99 from map_ofNat C 99,
      show (C (108 : ℤ) : ℤ⟦X⟧) = 108 from map_ofNat C 108]
    ring
  have eB : (1 + 15 * X - 54 * X ^ 2 + 54 * X ^ 3 - 18 * X ^ 4 : ℤ⟦X⟧) = 1 + C (15 : ℤ) * X ^ 1 - C (54 : ℤ) * X ^ 2 + C (54 : ℤ) * X ^ 3 - C (18 : ℤ) * X ^ 4 := by
    rw [show (C (15 : ℤ) : ℤ⟦X⟧) = 15 from map_ofNat C 15,
      show (C (18 : ℤ) : ℤ⟦X⟧) = 18 from map_ofNat C 18,
      show (C (54 : ℤ) : ℤ⟦X⟧) = 54 from map_ofNat C 54]
    ring
  have h := congrArg (coeff (m + 5)) ode
  rw [e, eB] at h
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_X_pow,
    coeff_one, coeff_A, coeff_T, show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega, show 3 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, show 5 ≤ m + 5 by omega, if_true,
    show m + 5 ≠ 0 by omega, show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega, show m + 5 ≠ 4 by omega, if_false,
    show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega,
    show m + 1 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 3 ≠ 0 by omega, show m + 4 ≠ 0 by omega, show m + 5 ≠ 0 by omega] at h
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega]
  push_cast at h ⊢
  linear_combination h

/-- Controls: a(0..5) = 1, 10, 19, 136, 649, 4375 as in the entry's data. -/
lemma controls : a 0 = 1 ∧ a 1 = 10 ∧ a 2 = 19 ∧ a 3 = 136 ∧ a 4 = 649 ∧
    a 5 = 4375 := by
  have h4 : a 4 = 649 := by
    have h := a_rec 2
    simp [Finset.sum_range_succ, a_zero, a_one, a_two, a_three] at h
    linarith
  have h5 : a 5 = 4375 := by
    have h := a_rec 3
    simp [Finset.sum_range_succ, a_zero, a_one, a_two, a_three, h4] at h
    linarith
  exact ⟨a_zero, a_one, a_two, a_three, h4, h5⟩

/-- Mathar's conjecture: the recurrence holds for every n >= 5. -/
theorem conjecture : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 1) * a n +
      (2 - 7 * (n : ℤ)) * a (n - 1) +
      3 * (17 - 7 * (n : ℤ)) * a (n - 2) +
      9 * (11 * (n : ℤ) - 34) * a (n - 3) +
      108 * (4 - (n : ℤ)) * a (n - 4) +
      36 * ((n : ℤ) - 5) * a (n - 5) = 0 :=
  recurrence

end OMA.S_oeis_a177203

theorem OMA.solution : type_of% @OMA.S_oeis_a177203.main :=
  OMA.S_oeis_a177203.conjecture
