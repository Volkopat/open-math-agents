import Mathlib

/-!
# A139399: Number of steps to reach a cycle in Collatz problem.

Source: https://oeis.org/A139399
Credit: @agchua

Comment line of A139399:
  a(n) = A006577(n) - 2 for n > 2 (if the conjecture holds).
Offset 1. The conjecture meant is the Collatz (3x+1) conjecture: every trajectory of the map A006370,
x -> x/2 for even x and x -> 3x+1 for odd x, reaches 1. The statement below asserts the claim for
every n > 2 whose own trajectory reaches 1, so it contains the claim under the Collatz conjecture.
Definitions, as in the entry and its programs: A006577(n) is the number of steps to reach 1, the
least k with f^k(n) = 1 (its value -1 for a trajectory that never reaches 1 does not occur under the
hypothesis). a(n) is the number of steps to reach the cycle 1 -> 4 -> 2 -> 1, the least k with f^k(n)
in {1, 2, 4}, as in the entry's Haskell program (so a(1) = a(2) = a(4) = 0, as the entry says); a
trajectory that reaches 1 meets no other cycle before it. Both are written as sInf of the set of such k.
-/

namespace OMA.S_oeis_a139399

/-- A006370: the Collatz map. -/
def f (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- A006577: the number of steps of f to reach 1. -/
noncomputable def A006577 (n : ℕ) : ℕ := sInf {k : ℕ | f^[k] n = 1}

/-- A139399: the number of steps of f to reach the cycle 1 -> 4 -> 2 -> 1. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | f^[k] n = 1 ∨ f^[k] n = 2 ∨ f^[k] n = 4}

/-- a(n) = A006577(n) - 2 for n > 2, for every n whose trajectory reaches 1. -/
theorem main : ∀ n : ℕ, 2 < n → (∃ k : ℕ, f^[k] n = 1) →
    (a n : ℤ) = (A006577 n : ℤ) - 2 := by
  sorry

end OMA.S_oeis_a139399
