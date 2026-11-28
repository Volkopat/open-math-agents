import OMAStatements.S_oeis_a163198
import Mathlib

-- Proof of the formula in OEIS A163198 (statement by @ivillar).
-- Idea: induction on n; with x = F(2n+1), y = F(2n+2), F(2n+3) = x + y, the step reduces to
-- 3y(x^2 + xy - y^2 - 1) = 0, which is Cassini's identity y^2 - xy - x^2 = (-1)^(2n+1).

namespace OMAA163198Helpers

open OMA.S_oeis_a163198

theorem cassini (m : ℕ) : (Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib m * Nat.fib (m + 1) - (Nat.fib m : ℤ) ^ 2 =
    (-1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + 1 = m + 2 by ring, Nat.fib_add_two, pow_succ]
    push_cast
    linear_combination -ih

end OMAA163198Helpers

open OMA.S_oeis_a163198 OMAA163198Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a163198.main := by
  intro n
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have hs : a (n + 1) = a n + Nat.fib (2 * (n + 1)) ^ 3 := by
      unfold a
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hy : Nat.fib (2 * (n + 1)) = Nat.fib (2 * n + 1 + 1) := by ring_nf
    have hz : Nat.fib (2 * (n + 1) + 1) = Nat.fib (2 * n + 1) + Nat.fib (2 * n + 1 + 1) := by
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, Nat.fib_add_two]
    have c := cassini (2 * n + 1)
    have hc : ((-1 : ℤ) ^ (2 * n + 1)) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [hc] at c
    rw [hs, hz]
    push_cast
    rw [ih, hy]
    generalize Nat.fib (2 * n + 1) = x at c ⊢
    generalize Nat.fib (2 * n + 1 + 1) = y at c ⊢
    have c' : ((y : ℤ) : ℚ) ^ 2 - ((x : ℤ) : ℚ) * ((y : ℤ) : ℚ) - ((x : ℤ) : ℚ) ^ 2 = -1 := by
      exact_mod_cast c
    push_cast at c'
    linear_combination (3 / 4 * (y : ℚ)) * c'
