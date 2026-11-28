import OMAStatements.S_oeis_a174808

namespace OMA.S_oeis_a174808

open PowerSeries


/-- The large Schroeder g.f. over Z. -/
noncomputable def R : ℤ⟦X⟧ := PowerSeries.mk fun k => (Nat.largeSchroder k : ℤ)

lemma coeff_R (n : ℕ) : coeff n R = (Nat.largeSchroder n : ℤ) := by simp [R]

lemma coeff_R_sq (n : ℕ) : coeff n (R ^ 2) =
    ∑ k ∈ Finset.range (n + 1), (Nat.largeSchroder k : ℤ) * (Nat.largeSchroder (n - k) : ℤ) := by
  rw [sq, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i R * coeff j R)]
  simp only [coeff_R]

lemma r_succ (n : ℕ) : (Nat.largeSchroder (n + 1) : ℤ) = (Nat.largeSchroder n : ℤ) +
    ∑ k ∈ Finset.range (n + 1), (Nat.largeSchroder k : ℤ) * (Nat.largeSchroder (n - k) : ℤ) := by
  rw [Nat.largeSchroder]
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun k => (Nat.largeSchroder k : ℤ) * (Nat.largeSchroder (n - k) : ℤ))]

/-- The Schroeder quadratic x R^2 + (x - 1) R + 1 = 0. -/
lemma hQR : X * R ^ 2 + (X - 1) * R + 1 = 0 := by
  have e : X * R ^ 2 + (X - 1) * R + 1 = R ^ 2 * X ^ 1 + R * X ^ 1 - R + 1 := by ring
  rw [e]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_one, map_zero]
  rcases n with _ | n
  · simp [coeff_R]
  · simp only [show 1 ≤ n + 1 by omega, if_true, show n + 1 - 1 = n by omega,
      show n + 1 ≠ 0 by omega, if_false, coeff_R]
    rw [r_succ, coeff_R_sq]
    ring

/-- The substituted series y = x + x^2. -/
noncomputable def y : ℤ⟦X⟧ := X + X ^ 2

lemma hy : HasSubst y := HasSubst.of_constantCoeff_zero' (by simp [y])

lemma coeff_one_add_X_pow (d m : ℕ) : coeff m ((1 + X : ℤ⟦X⟧) ^ d) = ((d.choose m : ℕ) : ℤ) := by
  have h : (1 + X : ℤ⟦X⟧) ^ d = (((1 + Polynomial.X) ^ d : Polynomial ℤ) : ℤ⟦X⟧) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

lemma coeff_y_pow (n d : ℕ) :
    coeff n (y ^ d) = if d ≤ n then ((d.choose (n - d) : ℕ) : ℤ) else 0 := by
  rw [y, show (X + X ^ 2 : ℤ⟦X⟧) = (1 + X) * X by ring, mul_pow, coeff_mul_X_pow']
  split_ifs
  · rw [coeff_one_add_X_pow]
  · rfl

/-- The g.f. of A174808 as R(x + x^2). -/
noncomputable def A : ℤ⟦X⟧ := R.subst y

lemma coeff_A (n : ℕ) : coeff n A = a n := by
  rw [A, coeff_subst' hy, finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · unfold a
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [coeff_R, coeff_y_pow, if_pos (by simp at hk; omega), smul_eq_mul]
    ring
  · intro d hd
    simp only [Function.mem_support, ne_eq] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hd
    rw [coeff_y_pow, if_neg (by omega), smul_zero]

/-- The quadratic equation y A^2 + (y - 1) A + 1 = 0. -/
lemma quad : (X + X ^ 2) * A ^ 2 + (X + X ^ 2 - 1) * A + 1 = 0 := by
  have h : (X * R ^ 2 + (X - 1) * R + 1).subst y = (0 : ℤ⟦X⟧).subst y := by rw [hQR]
  rw [subst_add hy, subst_add hy, subst_mul hy, subst_mul hy, subst_pow hy, subst_sub hy,
    subst_X hy] at h
  have h1 : (1 : ℤ⟦X⟧).subst y = (1 : ℤ⟦X⟧) := by
    rw [show (1 : ℤ⟦X⟧) = C (1 : ℤ) from (map_one C).symm, subst_C]
    simp
  have h0 : (0 : ℤ⟦X⟧).subst y = (0 : ℤ⟦X⟧) := by
    rw [show (0 : ℤ⟦X⟧) = C (0 : ℤ) from (map_zero C).symm, subst_C]
    simp
  rw [h1, h0] at h
  rw [A, ← h, y]

@[simp] lemma d_ofNat (n : ℕ) [n.AtLeastTwo] :
    d⁄dX ℤ (no_index (OfNat.ofNat n : ℤ⟦X⟧)) = 0 :=
  Derivation.map_natCast _ n

/-- The derivative of the quadratic equation. -/
lemma dquad : (1 + 2 * X) * A ^ 2 +
    (2 * (X + X ^ 2) * A + (X + X ^ 2 - 1)) * d⁄dX ℤ A + (1 + 2 * X) * A = 0 := by
  have e : (1 + 2 * X) * A ^ 2 +
      (2 * (X + X ^ 2) * A + (X + X ^ 2 - 1)) * d⁄dX ℤ A + (1 + 2 * X) * A =
      d⁄dX ℤ ((X + X ^ 2) * A ^ 2 + (X + X ^ 2 - 1) * A + 1) := by
    simp only [map_add, map_sub, map_neg, Derivation.leibniz, Derivation.leibniz_pow,
      derivative_X, Derivation.map_one_eq_zero, d_ofNat, smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [e, quad, map_zero]

/-- Mathar's recurrence as a differential equation: x C A' + D A = B. -/
lemma ode : X * (1 - 5 * X - 11 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4 + X ^ 5) * d⁄dX ℤ A +
    (1 - X - 9 * X ^ 2 - 6 * X ^ 3) * A = 1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 := by
  have key : (2 * (X + X ^ 2) * A + (X + X ^ 2 - 1)) *
      ((1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3) - (1 - X - 9 * X ^ 2 - 6 * X ^ 3) * A -
        X * (1 - 5 * X - 11 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4 + X ^ 5) * d⁄dX ℤ A) = 0 := by
    linear_combination (-1 - 2 * X + X ^ 2 + 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5) * quad -
      X * (1 - 5 * X - 11 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4 + X ^ 5) * dquad
  have hne : (2 * (X + X ^ 2) * A + (X + X ^ 2 - 1) : ℤ⟦X⟧) ≠ 0 := by
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
    ((n : ℤ) + 1) * a n + (-5 * (n : ℤ) + 4) * a (n - 1) + (-11 * (n : ℤ) + 13) * a (n - 2) +
      3 * (-(n : ℤ) + 1) * a (n - 3) + 3 * ((n : ℤ) - 4) * a (n - 4) +
      ((n : ℤ) - 5) * a (n - 5) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e : X * (1 - 5 * X - 11 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4 + X ^ 5) * d⁄dX ℤ A +
      (1 - X - 9 * X ^ 2 - 6 * X ^ 3) * A =
      X * d⁄dX ℤ A - C (5 : ℤ) * (X * d⁄dX ℤ A * X ^ 1) - C (11 : ℤ) * (X * d⁄dX ℤ A * X ^ 2) -
        C (3 : ℤ) * (X * d⁄dX ℤ A * X ^ 3) + C (3 : ℤ) * (X * d⁄dX ℤ A * X ^ 4) +
        (X * d⁄dX ℤ A * X ^ 5) + (A - (A * X ^ 1) - C (9 : ℤ) * (A * X ^ 2) -
        C (6 : ℤ) * (A * X ^ 3)) := by
    rw [show (C (3 : ℤ) : ℤ⟦X⟧) = 3 from map_ofNat C 3,
      show (C (5 : ℤ) : ℤ⟦X⟧) = 5 from map_ofNat C 5,
      show (C (6 : ℤ) : ℤ⟦X⟧) = 6 from map_ofNat C 6,
      show (C (9 : ℤ) : ℤ⟦X⟧) = 9 from map_ofNat C 9,
      show (C (11 : ℤ) : ℤ⟦X⟧) = 11 from map_ofNat C 11]
    ring
  have eB : (1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 : ℤ⟦X⟧) =
      1 + C (3 : ℤ) * X ^ 1 + C (3 : ℤ) * X ^ 2 + C (2 : ℤ) * X ^ 3 := by
    rw [show (C (2 : ℤ) : ℤ⟦X⟧) = 2 from map_ofNat C 2,
      show (C (3 : ℤ) : ℤ⟦X⟧) = 3 from map_ofNat C 3]
    ring
  have h := congrArg (coeff (m + 5)) ode
  rw [e, eB] at h
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_X_pow,
    coeff_one, coeff_A, coeff_T, show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega,
    show 3 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, show 5 ≤ m + 5 by omega, if_true,
    show m + 5 ≠ 0 by omega, if_false,
    show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    show m + 5 - 5 = m by omega, show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega,
    show m + 2 ≠ 0 by omega] at h
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
    show m + 5 - 5 = m by omega]
  push_cast at h ⊢
  linear_combination h

/-- Controls: a(0..5) = 1, 2, 8, 34, 162, 820 as in the entry. -/
lemma controls : a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 8 ∧ a 3 = 34 ∧ a 4 = 162 ∧ a 5 = 820 := by
  have r0 : (Nat.largeSchroder 0 : ℤ) = 1 := by simp
  have r1 : (Nat.largeSchroder 1 : ℤ) = 2 := by simp
  have r2 : (Nat.largeSchroder 2 : ℤ) = 6 := by simp
  have r3 : (Nat.largeSchroder 3 : ℤ) = 22 := by
    rw [r_succ]; simp [Finset.sum_range_succ, r0, r1, r2]
  have r4 : (Nat.largeSchroder 4 : ℤ) = 90 := by
    rw [r_succ]; simp [Finset.sum_range_succ, r0, r1, r2, r3]
  have r5 : (Nat.largeSchroder 5 : ℤ) = 394 := by
    rw [r_succ]; simp [Finset.sum_range_succ, r0, r1, r2, r3, r4]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [a, Finset.sum_range_succ, Nat.choose, r0, r1, r2, r3, r4, r5]

/-- Mathar's conjecture: the recurrence holds for every n >= 5. -/
theorem conjecture : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 1) * a n + (-5 * (n : ℤ) + 4) * a (n - 1) + (-11 * (n : ℤ) + 13) * a (n - 2) +
      3 * (-(n : ℤ) + 1) * a (n - 3) + 3 * ((n : ℤ) - 4) * a (n - 4) +
      ((n : ℤ) - 5) * a (n - 5) = 0 :=
  recurrence

end OMA.S_oeis_a174808

theorem OMA.solution : type_of% @OMA.S_oeis_a174808.main :=
  OMA.S_oeis_a174808.conjecture
