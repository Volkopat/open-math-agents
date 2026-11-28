import Mathlib

/-!
# A382407: a(n) is the number of partitions n = x + y + z of positive integers such that x*y + y*z + x*z is a perfect square.

Source: https://oeis.org/A382407
Credit: @agchua

Comment of A382407 (unsigned; the entry is by Felix Huber, Apr 04 2025):
  Conjecture: a(k) = 0 iff k is an element of {2, 4, 8, 13} union A000244 union A005030.
A000244 is the powers of 3, a(n) = 3^n for n >= 0; A005030 is a(n) = 5*3^n for n >= 0.
The sequence has offset 1, so the claim is stated for k >= 1. As in the entry's Maple program
(x from 1 to n/3, y from x to (n-x)/2, z = n-x-y), a partition is counted once, as a triple
x <= y <= z of positive integers with sum n; the value x*y + y*z + x*z is a perfect square when it
is r*r for a natural number r (IsSquare).
-/

namespace OMA.S_oeis_a382407

/-- A382407(n): the number of triples 1 <= x <= y <= z with x + y + z = n and x*y + y*z + x*z a
perfect square. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun t : ℕ × ℕ × ℕ =>
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n ∧
      IsSquare (t.1 * t.2.1 + t.2.1 * t.2.2 + t.1 * t.2.2))).card

/-- The comment's conjecture: for k >= 1, a(k) = 0 iff k is 2, 4, 8 or 13, a power of 3, or
5 times a power of 3. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    (a k = 0 ↔ k ∈ ({2, 4, 8, 13} : Set ℕ) ∨ (∃ j : ℕ, k = 3 ^ j) ∨ (∃ j : ℕ, k = 5 * 3 ^ j)) := by
  sorry

end OMA.S_oeis_a382407
