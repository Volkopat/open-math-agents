import Mathlib

/-!
# A260119: a(n) is the least positive integer k such that 2^n-1 and k^n-1 are relatively prime.

Source: https://oeis.org/A260119

Conjecture in the entry (David A. Corneth, Aug 17 2015):
Conjecture 1: a(n) is never divisible by 2.

Formalization notes:
* Offset 1. The claim is made for every n ≥ 1. For n = 0 both 2^0-1 and k^0-1 are 0, so no
  k exists, and n = 0 is outside the range of the sequence.
* `a n` is defined by the name of the entry: the infimum of the set of positive natural
  numbers k with Nat.Coprime (2^n - 1) (k^n - 1). Since k ≥ 1 and 2 ≥ 1, both k^n ≥ 1 and
  2^n ≥ 1, so the natural-number subtractions 2^n - 1 and k^n - 1 are exact.
* For n ≥ 1 the set is nonempty (the entry notes that k = 2^n - 1 works), so `a n` is its
  least element. This is not assumed in the definition: if the set were empty, `sInf` would
  give 0, which is even, so the statement does not hold trivially.
* Never divisible by 2 is stated as `Odd (a n)`.
-/

namespace OMA.S_oeis_a260119

/-- A260119: the least positive integer k such that 2^n - 1 and k^n - 1 are coprime. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ Nat.Coprime (2 ^ n - 1) (k ^ n - 1)}

/-- Corneth's Conjecture 1 on A260119: a(n) is odd for every n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Odd (a n) := by
  sorry

end OMA.S_oeis_a260119
