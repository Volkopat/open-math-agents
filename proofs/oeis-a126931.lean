import OMAStatements.S_oeis_a126931
import Mathlib

/-
A126931: a sequence defined by a convolution recurrence satisfies the stated recurrence with
polynomial coefficients.

Let A be the generating function with rational coefficients.
- hFE: the defining recurrence says (-3 * X + 10 * X ^ 2) A^2 + (-1 + 6 * X) A + (1) = 0, checked coefficient by
  coefficient (the convolution sum is the coefficient of A^2).
- Then S = 2 (-3 * X + 10 * X ^ 2) A + (-1 + 6 * X) satisfies S^2 = R with R = 1 - 4 * X ^ 2.
- ode, odeA: differentiating S^2 = R gives 2 R S' = R' S, hence a first-order linear equation
  for A with polynomial coefficients; a common polynomial factor is cancelled.
- Comparing the coefficient of X^m on both sides gives the recurrence, up to a rational factor.
-/

namespace OMA.P126931

open PowerSeries

lemma ode (R S : PowerSeries ℚ) (hS : S ^ 2 = R) :
    2 * R * d⁄dX ℚ S = d⁄dX ℚ R * S := by
  have h := congrArg (d⁄dX ℚ) hS
  rw [derivative_pow] at h
  have h' : 2 * S * d⁄dX ℚ S = d⁄dX ℚ R := by simpa using h
  calc 2 * R * d⁄dX ℚ S = S * (2 * S * d⁄dX ℚ S) := by
        rw [← hS]
        ring
    _ = S * d⁄dX ℚ R := by rw [h']
    _ = d⁄dX ℚ R * S := mul_comm _ _

lemma odeA (R S U V W A : PowerSeries ℚ) (hS : S ^ 2 = R) (hA : A * W = U + V * S) :
    2 * R * V * W * d⁄dX ℚ A +
        (2 * R * V * d⁄dX ℚ W - (2 * R * d⁄dX ℚ V + V * d⁄dX ℚ R) * W) * A =
      2 * R * V * d⁄dX ℚ U - (2 * R * d⁄dX ℚ V + V * d⁄dX ℚ R) * U := by
  have h1 := ode R S hS
  have h2 := congrArg (d⁄dX ℚ) hA
  rw [Derivation.leibniz, map_add, Derivation.leibniz] at h2
  simp only [smul_eq_mul] at h2
  linear_combination (2 * R * V) * h2 + V ^ 2 * h1 - (2 * R * d⁄dX ℚ V + V * d⁄dX ℚ R) * hA

lemma d_ofNat (n : ℕ) [n.AtLeastTwo] :
    d⁄dX ℚ (no_index (OfNat.ofNat n) : ℚ⟦X⟧) = 0 := by
  rw [← map_ofNat (C (R := ℚ)) n, derivative_C]


lemma main' (a : ℕ → ℤ) (h0 : a 0 = 1) (h1 : a 1 = 3)
    (hrec : ∀ n, a (n + 2) = 6 * a (n + 1) - 3 * ∑ k : Fin (n + 2), a k * a (n + 1 - k) + 10 * ∑ k : Fin (n + 1), a k * a (n - k)) :
    ∀ n : ℕ, 3 ≤ n →
      3 * ((n : ℤ) + 1) * a n + 10 * (-(n : ℤ) - 1) * a (n - 1) + 12 * (-(n : ℤ) + 2) * a (n - 2)
      + 40 * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℚ⟦X⟧, A = PowerSeries.mk (fun n => (a n : ℚ)) := ⟨_, rfl⟩
  have hcA : ∀ n, coeff n A = (a n : ℚ) := fun n => by rw [hAdef, coeff_mk]
  have hcc : constantCoeff A = (a 0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply, hcA]
  have hconv : ∀ m, coeff m (A ^ 2) =
      ∑ k ∈ Finset.range (m + 1), (a k : ℚ) * (a (m - k) : ℚ) := by
    intro m
    rw [pow_two, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i A * coeff j A)]
    simp only [hcA]
  have e0 : ∀ n, (∑ k : Fin (n + 1), (a k : ℚ) * (a (n - k) : ℚ)) =
      ∑ k ∈ Finset.range (n + 1), (a k : ℚ) * (a (n - k) : ℚ) := fun n =>
    Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * (a (n - k) : ℚ)) (n + 1)
  have e1 : ∀ n, (∑ k : Fin (n + 2), (a k : ℚ) * (a (n + 1 - k) : ℚ)) =
      ∑ k ∈ Finset.range (n + 1 + 1), (a k : ℚ) * (a (n + 1 - k) : ℚ) := fun n =>
    Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * (a (n + 1 - k) : ℚ)) (n + 2)
  have hrecQ : ∀ n, coeff (n + 2) A = 6 * coeff (n + 1) A - 3 * coeff (n + 1) (A ^ 2) + 10 * coeff n (A ^ 2) := by
    intro n
    simp only [hcA, hconv]
    rw [hrec n]
    push_cast
    simp only [e0, e1]
  have hFE : C (-3 : ℚ) * (A ^ 2 * X ^ 1) +
      C (10 : ℚ) * (A ^ 2 * X ^ 2) +
      C (-1 : ℚ) * (A * X ^ 0) +
      C (6 : ℚ) * (A * X ^ 1) +
      C (1 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 0) = 0 := by
    ext m
    rcases m with _ | _ | k
    · simp [coeff_C_mul, coeff_mul_X_pow', coeff_one, hcA, hcc, hconv, h0, h1, Finset.sum_range_succ] <;> norm_num
    · simp [coeff_C_mul, coeff_mul_X_pow', coeff_one, hcA, hcc, hconv, h0, h1, Finset.sum_range_succ] <;> norm_num
    · have fa1 : coeff (k + 1 + 1) (C (-3 : ℚ) * (A ^ 2 * X ^ 1)) = (-3 : ℚ) * coeff (k + 1) (A ^ 2) := by
        have e : k + 1 + 1 = k + 1 + 1 := by omega
        conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
      have fa2 : coeff (k + 1 + 1) (C (10 : ℚ) * (A ^ 2 * X ^ 2)) = (10 : ℚ) * coeff (k) (A ^ 2) := by
        have e : k + 1 + 1 = k + 2 := by omega
        conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
      have fb0 : coeff (k + 1 + 1) (C (-1 : ℚ) * (A * X ^ 0)) = (-1 : ℚ) * coeff (k + 2) (A) := by
        have e : k + 1 + 1 = k + 2 + 0 := by omega
        conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
      have fb1 : coeff (k + 1 + 1) (C (6 : ℚ) * (A * X ^ 1)) = (6 : ℚ) * coeff (k + 1) (A) := by
        have e : k + 1 + 1 = k + 1 + 1 := by omega
        conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
      have fg0 : coeff (k + 1 + 1) (C (1 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 0)) = 0 := by
        have e : k + 1 + 1 = k + 2 + 0 := by omega
        rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
      simp only [map_add, map_zero, fa1, fa2, fb0, fb1, fg0]
      linear_combination (-1 : ℚ) * hrecQ k
  have hFE' : (-3 * X + 10 * X ^ 2) * A ^ 2 + (-1 + 6 * X) * A + (1) = 0 := by
    simp only [map_neg, map_ofNat, map_one, map_zero] at hFE
    linear_combination hFE
  obtain ⟨S, hSdef⟩ : ∃ S : ℚ⟦X⟧, S = 2 * (-3 * X + 10 * X ^ 2) * A + (-1 + 6 * X) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℚ⟦X⟧, R = 1 - 4 * X ^ 2 := ⟨_, rfl⟩
  have hS : S ^ 2 = R := by
    rw [hSdef, hR]
    linear_combination (4 * (-3 * X + 10 * X ^ 2)) * hFE'
  have hA : A * (-6 * X + 20 * X ^ 2) = (1 - 6 * X) + (1) * S := by
    rw [hSdef]
    ring
  have hode := odeA R S (1 - 6 * X) (1) (-6 * X + 20 * X ^ 2) A hS hA
  have dR : d⁄dX ℚ R = -8 * X := by
    rw [hR]
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dU : d⁄dX ℚ (1 - 6 * X : ℚ⟦X⟧) = -6 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dV : d⁄dX ℚ (1 : ℚ⟦X⟧) = 0 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dW : d⁄dX ℚ (-6 * X + 20 * X ^ 2 : ℚ⟦X⟧) = -6 + 40 * X := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  rw [dR] at hode
  simp only [dU, dV, dW] at hode
  rw [hR] at hode
  have key : C (-12 : ℚ) * (d⁄dX ℚ A * X ^ 1) +
      C (40 : ℚ) * (d⁄dX ℚ A * X ^ 2) +
      C (48 : ℚ) * (d⁄dX ℚ A * X ^ 3) +
      C (-160 : ℚ) * (d⁄dX ℚ A * X ^ 4) +
      C (-12 : ℚ) * (A * X ^ 0) +
      C (80 : ℚ) * (A * X ^ 1) +
      C (-160 : ℚ) * (A * X ^ 3) =
      C (-12 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 0) +
      C (8 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 1) := by
    simp only [map_neg, map_ofNat, map_one, map_zero]
    linear_combination (1 : ℚ⟦X⟧) * hode
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have tp1 : coeff (k + 3) (C (-12 : ℚ) * (d⁄dX ℚ A * X ^ 1)) =
      (-12 : ℚ) * (coeff (k + 3) A * ((k : ℚ) + 3)) := by
    have e : k + 3 = k + 2 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 2 + 1 = k + 3 by omega]; push_cast; ring)
  have tp2 : coeff (k + 3) (C (40 : ℚ) * (d⁄dX ℚ A * X ^ 2)) =
      (40 : ℚ) * (coeff (k + 2) A * ((k : ℚ) + 2)) := by
    have e : k + 3 = k + 1 + 2 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 1 + 1 = k + 2 by omega]; push_cast; ring)
  have tp3 : coeff (k + 3) (C (48 : ℚ) * (d⁄dX ℚ A * X ^ 3)) =
      (48 : ℚ) * (coeff (k + 1) A * ((k : ℚ) + 1)) := by
    have e : k + 3 = k + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (push_cast; ring)
  have tp4 : coeff (k + 3) (C (-160 : ℚ) * (d⁄dX ℚ A * X ^ 4)) =
      (-160 : ℚ) * (coeff k A * ((k : ℚ) + 0)) := by
    rcases k with _ | k'
    · simp [coeff_C_mul, coeff_mul_X_pow']
    · have e : k' + 1 + 3 = k' + 4 := by omega
      conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
      all_goals (push_cast; ring)
  have tq0 : coeff (k + 3) (C (-12 : ℚ) * (A * X ^ 0)) = (-12 : ℚ) * coeff (k + 3) A := by
    have e : k + 3 = k + 3 + 0 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq1 : coeff (k + 3) (C (80 : ℚ) * (A * X ^ 1)) = (80 : ℚ) * coeff (k + 2) A := by
    have e : k + 3 = k + 2 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq3 : coeff (k + 3) (C (-160 : ℚ) * (A * X ^ 3)) = (-160 : ℚ) * coeff (k) A := by
    have e : k + 3 = k + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have th0 : coeff (k + 3) (C (-12 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 0)) = 0 := by
    have e : k + 3 = k + 3 + 0 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th1 : coeff (k + 3) (C (8 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 1)) = 0 := by
    have e : k + 3 = k + 2 + 1 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have hc := congrArg (coeff (k + 3)) key
  simp only [map_add, map_zero, tp1, tp2, tp3, tp4, tq0, tq1, tq3, th0, th1] at hc
  simp only [hcA] at hc
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
  apply Int.cast_injective (α := ℚ)
  push_cast at hc ⊢
  linear_combination (-1 / 4 : ℚ) * hc

end OMA.P126931

theorem OMA.solution : type_of% @OMA.S_oeis_a126931.main :=
  OMA.P126931.main' OMA.S_oeis_a126931.a (by rw [OMA.S_oeis_a126931.a]) (by rw [OMA.S_oeis_a126931.a])
    (fun n => by rw [OMA.S_oeis_a126931.a])
