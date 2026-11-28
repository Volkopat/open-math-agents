import OMAStatements.S_oeis_a192466
import Mathlib

-- Proof of Colin Barker's conjectures in OEIS A192466 (statement by @ivillar).
-- Idea: x^2 - x - 2 = (x - 2)(x + 1), so the remainder r = c1*x + c0 of f modulo it satisfies
-- r(2) = f(2) and r(-1) = f(-1); hence 3*c1 = f(2) - f(-1) = 2^n + 4^n - (-1)^n - 1.

namespace OMAA192466Helpers

open Polynomial OMA.S_oeis_a192466

theorem hq2 : (X ^ 2 - X - 2 : ℤ[X]).natDegree = 2 := by compute_degree!

theorem coeff1_eq (f : ℤ[X]) :
    3 * (f %ₘ (X ^ 2 - X - 2)).coeff 1 = eval 2 f - eval (-1) f := by
  have hm : (X ^ 2 - X - 2 : ℤ[X]).Monic := by monicity!
  have hne : (X ^ 2 - X - 2 : ℤ[X]) ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hq2, natDegree_one] at this
    omega
  have hdeg : (f %ₘ (X ^ 2 - X - 2)).natDegree ≤ 1 := by
    have := natDegree_modByMonic_lt f hm hne
    rw [hq2] at this
    omega
  have q2 : eval 2 (X ^ 2 - X - 2 : ℤ[X]) = 0 := by norm_num
  have qm : eval (-1) (X ^ 2 - X - 2 : ℤ[X]) = 0 := by norm_num
  have h2 : eval 2 (f %ₘ (X ^ 2 - X - 2)) = eval 2 f := by
    conv_rhs => rw [← modByMonic_add_div f (X ^ 2 - X - 2)]
    rw [eval_add, eval_mul, q2, zero_mul, add_zero]
  have h1 : eval (-1) (f %ₘ (X ^ 2 - X - 2)) = eval (-1) f := by
    conv_rhs => rw [← modByMonic_add_div f (X ^ 2 - X - 2)]
    rw [eval_add, eval_mul, qm, zero_mul, add_zero]
  rw [eq_X_add_C_of_natDegree_le_one hdeg] at h2 h1
  simp only [eval_add, eval_mul, eval_C, eval_X] at h2 h1
  linear_combination h2 - h1

theorem three_a (n : ℕ) : 3 * a n = 2 ^ n + 4 ^ n - (-1) ^ n - 1 := by
  have h := coeff1_eq (p n)
  have ev2 : eval 2 (p n) = 1 + 2 ^ n + 4 ^ n := by norm_num [p, pow_mul]
  have evm : eval (-1) (p n) = 1 + (-1) ^ n + 1 := by simp [p, pow_mul]
  rw [ev2, evm] at h
  unfold a reduce
  linear_combination h

theorem a_closed (n : ℕ) : (a n : ℚ) = (-1 - (-1) ^ n + 2 ^ n + 4 ^ n) / 3 := by
  have h := congrArg (Int.cast : ℤ → ℚ) (three_a n)
  push_cast at h
  rw [eq_div_iff (by norm_num)]
  linear_combination h

end OMAA192466Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a192466.main := by
  refine ⟨fun n _ => OMAA192466Helpers.a_closed n, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
  have : (OMA.S_oeis_a192466.a (m + 5) : ℚ) = 6 * OMA.S_oeis_a192466.a (m + 4) -
      7 * OMA.S_oeis_a192466.a (m + 3) - 6 * OMA.S_oeis_a192466.a (m + 2) +
      8 * OMA.S_oeis_a192466.a (m + 1) := by
    rw [OMAA192466Helpers.a_closed, OMAA192466Helpers.a_closed, OMAA192466Helpers.a_closed,
      OMAA192466Helpers.a_closed, OMAA192466Helpers.a_closed]
    ring
  exact_mod_cast this
