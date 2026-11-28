import Mathlib

/-!
# A389591: Sum of the divisors r of n such that r is not greater than twice the adjacent previous divisor of n.

Source: https://oeis.org/A389591
Credit: @agchua

Formula line of A389591 (the entry is by Omar E. Pol, Oct 08 2025):
  a(n) = A000203(n) - A379379(n). (Conjectured).
A389591 has offset 1, so the claim is stated for n ≥ 1. For a divisor r of n, the adjacent
previous divisor is the largest divisor of n below r. The divisor r = 1 has no previous divisor
and is not counted (as in the entry's PARI program, which adds d[k] only for k > 1); the
condition 1 < r is written out. `prevDiv n r` is the largest divisor of n below r (0 if there
is none, which happens only for r ≤ 1).

The referenced sequences, by their own entries' definitions:
* A000203 is sigma(n), the sum of the divisors of n: Mathlib's `ArithmeticFunction.sigma 1`.
* A379379 (offset 1) is the sum of the odd divisors of n except the e odd divisors described in
  A005279 (the name of A379379 puts the letter e in quotation marks). A005279 is the list of the
  numbers having divisors d, e with d < e < 2*d. So an e divisor of n is a divisor e of n for
  which some divisor d of n has d < e < 2*d, and A379379(n) is the sum of the odd divisors e of
  n for which no divisor d of n has d < e < 2*d.
-/

namespace OMA.S_oeis_a389591

/-- The adjacent previous divisor of r among the divisors of n: the largest divisor of n below
r, or 0 if there is none. -/
def prevDiv (n r : ℕ) : ℕ := ((Nat.divisors n).filter (fun d => d < r)).sup id

/-- A389591(n): the sum of the divisors r > 1 of n with r ≤ 2 * (the previous divisor of r). -/
def a (n : ℕ) : ℕ :=
  ∑ r ∈ (Nat.divisors n).filter (fun r => 1 < r ∧ r ≤ 2 * prevDiv n r), r

/-- A379379(n): the sum of the odd divisors e of n such that no divisor d of n has
d < e < 2*d. -/
def a379379 (n : ℕ) : ℕ :=
  ∑ e ∈ (Nat.divisors n).filter
    (fun e => Odd e ∧ ∀ d ∈ Nat.divisors n, ¬ (d < e ∧ e < 2 * d)), e

/-- The conjecture: a(n) = A000203(n) - A379379(n) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℤ) = (ArithmeticFunction.sigma 1 n : ℤ) - (a379379 n : ℤ) := by
  sorry

end OMA.S_oeis_a389591
