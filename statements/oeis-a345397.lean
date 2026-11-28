import Mathlib

/-!
# OEIS A345397: for every n there is a k with k, k^2, ..., k^n all digitally balanced in base 2

Source: https://oeis.org/A345397 (OEIS Foundation, CC BY-SA 4.0).
Credit: @corentingenton
Formalization: AI-generated with Claude Code (model claude-opus-5-5).

Entry A345397, offset 1: a(n) is the least number k such that {k, k^2, ..., k^n} are all
digitally balanced numbers in base 2 (A031443), or 0 if no such k exists.
Comment: Conjecture: all a(n) > 0. - Alex Ratushnyak, Apr 26 2022.
A031443: Digitally balanced numbers: positive numbers that in base 2 have the same number of
0's as 1's.

Formalization notes:
* `IsDigitallyBalanced m` is A031443: `m` is positive and its base-2 digits (`Nat.digits 2 m`,
  which has no leading zeros) contain as many 0's as 1's.
* a(n) > 0 means that a number k with the property exists; such a k is then positive, since
  k = k^1 must itself be balanced. The conjecture is stated for every n >= 1 (offset 1), with the
  powers k^i for 1 <= i <= n as in {k, k^2, ..., k^n}.
* Controls from the entry: a(1) = 2 (binary 10) and a(2) = 212 (binary 11010100, and
  212^2 = 44944 is 1010111110010000 in binary), matching the data 2, 212, 3274, 15113.
-/

namespace OMA.S_oeis_a345397

/-- A031443: a positive number whose binary expansion has as many 0's as 1's. -/
def IsDigitallyBalanced (m : ℕ) : Prop :=
  0 < m ∧ (Nat.digits 2 m).count 0 = (Nat.digits 2 m).count 1

/-- The conjecture all a(n) > 0: for every n >= 1 some k has k, k^2, ..., k^n all balanced. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, ∀ i : ℕ, 1 ≤ i → i ≤ n → IsDigitallyBalanced (k ^ i) := by
  sorry

end OMA.S_oeis_a345397
