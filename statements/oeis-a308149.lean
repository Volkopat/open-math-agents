import Mathlib

/-!
# A308149: Positive integers with Collatz trajectories that do not include the number 5.

Source: https://oeis.org/A308149
Credit: @agchua

Comment of A308149 (unsigned, verbatim):
  A consequence of the Collatz conjecture is that, after a(5), this would be equivalent to the
  list of positive integers with Collatz trajectories that include the number 32.

The sequence has offset 1 and lists in increasing order the n >= 1 whose trajectory
n, T(n), T(T(n)), ... (T the 3x+1 map) does not contain 5. The statement has two parts.
(1) The terms up to 16 are 1, 2, 4, 8, 16, so a(5) = 16 and the terms after a(5) are the
terms larger than 16. (2) The comment's claim: if the Collatz conjecture holds (every n >= 1
reaches 1), then the terms larger than 16 are exactly the positive integers whose trajectory
contains 32.
-/

namespace OMA.S_oeis_a308149

/-- The Collatz (3x+1) map. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The Collatz trajectory of n contains x. -/
def InTraj (n x : ℕ) : Prop := ∃ k : ℕ, T^[k] n = x

/-- (1) The first five terms are 1, 2, 4, 8, 16; (2) the comment's consequence of the Collatz
conjecture: after a(5) = 16 the terms are the positive integers whose trajectory contains 32. -/
theorem main :
    {n : ℕ | 1 ≤ n ∧ ¬ InTraj n 5 ∧ n ≤ 16} = {1, 2, 4, 8, 16} ∧
    ((∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, T^[k] n = 1) →
      {n : ℕ | 1 ≤ n ∧ ¬ InTraj n 5 ∧ 16 < n} = {n : ℕ | 1 ≤ n ∧ InTraj n 32}) := by
  sorry

end OMA.S_oeis_a308149
