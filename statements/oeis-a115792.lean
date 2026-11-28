import Mathlib

/-!
# A115792: a(n) = ceiling(g(A000073(n))) with g(k) = (k-1)^2/(4k).

Source: https://oeis.org/A115792
Credit: @JeremyDevs

Formalizes the conjecture of Chai Wah Wu (Dec 21 2023) recorded in OEIS A115792:
a(n) = a(n-2) + 2*a(n-3) + 2*a(n-4) + 2*a(n-5) + 2*a(n-6) + 2*a(n-7) + 3*a(n-8) + 2*a(n-9)
+ a(n-10) for n > 11.

Conventions:
* `T` is A000073, the tribonacci numbers with offset 0: T(0) = T(1) = 0, T(2) = 1 and
  T(n) = T(n-1) + T(n-2) + T(n-3), i.e. 0, 0, 1, 1, 2, 4, 7, 13, 24, ...
* The sequence has offset 2 and a(n) = ceiling((T(n) - 1)^2 / (4*T(n))), the ceiling of a rational
  number, taken in `ℚ` with values in `ℤ`: 0, 0, 1, 1, 2, 3, 6, 11, 20, 37, ... for n = 2, 3, ...
  The definition is written for every `n : ℕ`; at the unused indices n = 0, 1 one has T(n) = 0 and
  Lean's division by zero gives the junk value 0, which does not enter the statement.
* For n > 11 every index n - 2, ..., n - 10 is at least 2, so the natural-number subtractions are
  genuine and only terms of the sequence proper occur. This is exactly the stated range.
* Wu's second conjecture, the generating function
  x^4*(-x^2 - x - 1)/((x + 1)*(x^2 + 1)*(x^4 + 1)*(x^3 + x^2 + x - 1)), is not stated separately:
  its denominator expands to -(1 - x^2 - 2*x^3 - 2*x^4 - 2*x^5 - 2*x^6 - 2*x^7 - 3*x^8 - 2*x^9
  - x^10), so given the terms a(2), ..., a(11) it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a115792

/-- A000073, the tribonacci numbers: 0, 0, 1, 1, 2, 4, 7, 13, 24, 44, ... -/
def T : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => T (n + 2) + T (n + 1) + T n

/-- A115792 (offset 2): a(n) = ceiling((T(n) - 1)^2 / (4*T(n))). -/
def a (n : ℕ) : ℤ := ⌈((T n : ℚ) - 1) ^ 2 / (4 * (T n : ℚ))⌉

/-- Wu's conjectured linear recurrence of order 10, for `n > 11`. -/
theorem main : ∀ n : ℕ, 11 < n →
    a n = a (n - 2) + 2 * a (n - 3) + 2 * a (n - 4) + 2 * a (n - 5) + 2 * a (n - 6)
      + 2 * a (n - 7) + 3 * a (n - 8) + 2 * a (n - 9) + a (n - 10) := by
  sorry

end OMA.S_oeis_a115792
