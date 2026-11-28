import OMAStatements.S_oeis_a203157
import Mathlib

-- Problem: OEIS A203157 (statement with `products`): the (n-1)-st elementary symmetric function
-- of the first n triangular numbers. Writing products n = (P n, a n), P(n+1) = P(n) t(n+1) and
-- a(n+1) = a(n) t(n+1) + P(n), where 2 t(k) = k (k+1). By induction 2^n P(n) = n! (n+1)! and
-- 2^n a(n+1) = (n+1) ((n+1)!)^2, from which the recurrence follows.

namespace OMA.A203157

open OMA.S_oeis_a203157

lemma two_tri (k : ℕ) : 2 * tri k = (k : ℤ) * ((k : ℤ) + 1) := by
  induction k with
  | zero => simp [tri]
  | succ k ih => simp only [tri]; push_cast; linear_combination ih

lemma P_succ (n : ℕ) : (products (n + 1)).1 = (products n).1 * tri (n + 1) := rfl
lemma a_succ (n : ℕ) : a (n + 1) = a n * tri (n + 1) + (products n).1 := rfl

lemma prod_P (n : ℕ) : 2 ^ n * (products n).1 = (n.factorial : ℤ) * ((n + 1).factorial : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [P_succ, pow_succ,
      show 2 ^ n * 2 * ((products n).1 * tri (n + 1)) = (2 * tri (n + 1)) * (2 ^ n * (products n).1)
        by ring, ih, two_tri, Nat.factorial_succ (n + 1), Nat.factorial_succ n]
    push_cast; ring

lemma closed (n : ℕ) : 2 ^ n * a (n + 1) = ((n : ℤ) + 1) * ((n + 1).factorial : ℤ) ^ 2 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [a_succ, pow_succ,
      show 2 ^ m * 2 * (a (m + 1) * tri (m + 1 + 1) + (products (m + 1)).1) =
        (2 * tri (m + 1 + 1)) * (2 ^ m * a (m + 1)) + 2 ^ (m + 1) * (products (m + 1)).1 by ring,
      prod_P, ih, two_tri, Nat.factorial_succ (m + 1)]
    push_cast; ring

end OMA.A203157

theorem OMA.solution : type_of% @OMA.S_oeis_a203157.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  have h1 := OMA.A203157.closed (m + 1)
  have h0 := OMA.A203157.closed m
  have hp : (2 : ℤ) ^ (m + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hp
  rw [Nat.factorial_succ (m + 1)] at h1
  push_cast at h0 h1 ⊢
  linear_combination (-2 * ((m : ℤ) + 1)) * h1 + 2 * ((m : ℤ) + 2) ^ 3 * h0
