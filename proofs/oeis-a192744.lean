import OMAStatements.S_oeis_a192744
import Mathlib

/-!
Modulo the quadratic, two consecutive applications of the polynomial
recursion give an inhomogeneous Fibonacci recursion for the constant
coefficient. Its inhomogeneous term is the difference of two successive
factorials. The proposed recurrences are combinations of shifts of this
identity, with coefficients that cancel the factorial terms.
-/

namespace OMA.A192744

open Polynomial S_oeis_a192744

/-- The quadratic used to reduce the sequence polynomials. -/
noncomputable def q : ℤ[X] := X ^ 2 - X - 1

/-- Adding a constant to X leaves the degree at most one. -/
lemma degree_linear_le (c : ℤ) : degree (X + C c) ≤ (1 : WithBot ℕ) := by
  apply degree_add_le_of_degree_le
  · rw [degree_X]
    exact le_rfl
  · exact degree_C_le.trans (by decide : (0 : WithBot ℕ) ≤ 1)

/-- The divisor has degree two. -/
lemma degree_q : degree q = (2 : WithBot ℕ) := by
  have h : degree (X + (1 : ℤ[X])) < (2 : WithBot ℕ) := by
    simpa using (degree_linear_le 1).trans_lt (by decide : (1 : WithBot ℕ) < 2)
  rw [q, sub_sub, degree_sub_eq_left_of_degree_lt]
  · simp
  · simpa using h

/-- The divisor is monic, as its degree-two term has coefficient one. -/
lemma monic_q : q.Monic := by
  rw [q, sub_sub]
  exact monic_X_pow_sub (by
    simpa using (degree_linear_le 1).trans_lt (by decide : (1 : WithBot ℕ) < 2))

/-- The two-step difference reduces to a linear polynomial in X. -/
lemma fib_step (n : ℕ) :
    a (n + 2) - a (n + 1) - a n =
      ((n + 2).factorial : ℤ) - ((n + 1).factorial : ℤ) := by
  let f₁ : ℤ := (n + 1).factorial
  let f₂ : ℤ := (n + 2).factorial
  let r : ℤ[X] := X * C f₁ + C (f₂ - f₁)
  have hr : r %ₘ q = r := by
    apply (modByMonic_eq_self_iff monic_q).mpr
    rw [degree_q]
    apply (degree_add_le _ _).trans_lt
    apply max_lt
    · rw [mul_comm]
      exact (degree_C_mul_X_le f₁).trans_lt (by decide : (1 : WithBot ℕ) < 2)
    · exact (degree_C_le).trans_lt (by decide : (0 : WithBot ℕ) < 2)
  have hp : p (n + 2) - p (n + 1) - p n = q * p n + r := by
    rw [show p (n + 2) = X * p (n + 1) + C f₂ by rfl,
      show p (n + 1) = X * p n + C f₁ by rfl]
    simp only [q, r, map_sub]
    ring
  have hmod := congrArg (fun g : ℤ[X] => g %ₘ q) hp
  simp only [sub_modByMonic, add_modByMonic, self_mul_modByMonic monic_q, hr,
    zero_add] at hmod
  have hc := congrArg (fun g : ℤ[X] => g.coeff 0) hmod
  simpa [a, q, r, f₁, f₂, coeff_sub, coeff_add, coeff_mul_C] using hc

/-- The factorial difference factors using the one-step factorial recursion. -/
lemma scaled_step (n : ℕ) :
    a (n + 2) - a (n + 1) - a n = ((n : ℤ) + 1)^2 * (n.factorial : ℤ) := by
  rw [fib_step, Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  push_cast
  ring

end OMA.A192744

open OMA.S_oeis_a192744 OMA.A192744 in
theorem OMA.solution : type_of% @OMA.S_oeis_a192744.main := by
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    simp only [show ∀ k : ℕ, k + 4 - 1 = k + 3 by omega,
      show ∀ k : ℕ, k + 4 - 2 = k + 2 by omega,
      show ∀ k : ℕ, k + 4 - 3 = k + 1 by omega,
      show ∀ k : ℕ, k + 4 - 4 = k by omega, Nat.cast_add, Nat.cast_ofNat]
    have h₀ := scaled_step k
    have h₁ := scaled_step (k + 1)
    have h₂ := scaled_step (k + 2)
    rw [Nat.factorial_succ k] at h₁
    rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k] at h₂
    push_cast at h₁ h₂
    linear_combination h₂ - ((k : ℤ) + 5) * h₁ + ((k : ℤ) + 2) * h₀
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    simp only [show ∀ k : ℕ, k + 3 - 1 = k + 2 by omega,
      show ∀ k : ℕ, k + 3 - 2 = k + 1 by omega,
      show ∀ k : ℕ, k + 3 - 3 = k by omega, Nat.cast_add, Nat.cast_ofNat]
    have h₀ := scaled_step k
    have h₁ := scaled_step (k + 1)
    rw [Nat.factorial_succ k] at h₁
    push_cast at h₁
    linear_combination (-(k : ℤ) - 1) * h₁ + ((k : ℤ) + 2)^2 * h₀
