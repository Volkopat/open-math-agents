import Mathlib

/-!
# A193351: Numbers k such that A071324(k) is prime.

Source: https://oeis.org/A193351
Credit: @agchua

A071324(k) is the alternating sum of all divisors of k, the divisors in nonincreasing order,
starting with k (name of A071324, repeated in a comment of A193351); for example
A071324(169) = 169 - 13 + 1 = 157. A193351 has offset 1 and starts 3, 4, 8, 9, 16, 18, 49, ...

Unsigned comment lines of A193351 (the entry is by Michel Lagneau, Dec 20 2012), verbatim:
  It is interesting to note that all numbers except the first are squares, or twice a square,
  hence the conjecture:
  For k > 3, if the alternating sum of all divisors of k (divisors nonincreasing, starting with k)
  is a prime number, then k is either a square or twice a square.
The first term is 3 (A071324(3) = 3 - 1 = 2), so the claim is stated for k > 3.
-/

namespace OMA.S_oeis_a193351

/-- Alternating sum of a list with the first entry taken with sign plus:
altSum [x0, x1, x2, ...] = x0 - x1 + x2 - ... -/
noncomputable def altSum : List ℕ → ℤ
  | [] => 0
  | x :: l => (x : ℤ) - altSum l

/-- A071324(k): the alternating sum of the divisors of k, sorted in nonincreasing order,
so that k itself has sign plus. -/
noncomputable def A071324 (k : ℕ) : ℤ := altSum ((Nat.divisors k).sort (· ≥ ·))

/-- The conjecture: for k > 3, if A071324(k) is a prime number p, then k is a square or
twice a square. -/
theorem main : ∀ k p : ℕ, 3 < k → p.Prime → A071324 k = (p : ℤ) →
    (∃ m : ℕ, k = m ^ 2) ∨ (∃ m : ℕ, k = 2 * m ^ 2) := by
  sorry

end OMA.S_oeis_a193351
