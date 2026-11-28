import Mathlib

/-!
# A147792: A quadrisection of A061042.

Source: https://oeis.org/A147792
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A147792 (R. J. Mathar, Nov 14 2008):
a(n) = 3*a(n-2) -6*a(n-4) +10*a(n-6) -12*a(n-8) +12*a(n-10) -10*a(n-12) +6*a(n-14) - 3*a(n-16)
+a(n-18).

Conventions:
* A061042(n) is the denominator of 1/16 - 1/n^2 (offset 4), the denominator in lowest terms of
  a rational number: `((1 : ℚ) / 16 - 1 / (n : ℚ) ^ 2).den`.
* The sequence has offset 0 and, by the formula of the entry, a(n) = A061042(4n+4):
  1, 64, 18, 256, 50, 576, 49, 1024, 81, 1600, ...
* The entry states no range for the recurrence. It involves a(n-18) and the sequence starts at
  index 0, so it is stated for all n ≥ 18, the full range in which every term occurs; for
  such n the natural-number subtractions n - 2, ..., n - 18 are genuine.
* The recurrence has negative coefficients, so both sides are compared in `ℤ`.
-/

namespace OMA.S_oeis_a147792

/-- A061042: denominator of 1/16 - 1/n^2. -/
def A061042 (n : ℕ) : ℕ := ((1 : ℚ) / 16 - 1 / (n : ℚ) ^ 2).den

/-- A147792 (offset 0): a(n) = A061042(4n+4). -/
def a (n : ℕ) : ℕ := A061042 (4 * n + 4)

/-- Mathar's conjectured linear recurrence of order 18, for `n ≥ 18`. -/
theorem main : ∀ n : ℕ, 18 ≤ n →
    (a n : ℤ) = 3 * (a (n - 2) : ℤ) - 6 * (a (n - 4) : ℤ) + 10 * (a (n - 6) : ℤ)
      - 12 * (a (n - 8) : ℤ) + 12 * (a (n - 10) : ℤ) - 10 * (a (n - 12) : ℤ)
      + 6 * (a (n - 14) : ℤ) - 3 * (a (n - 16) : ℤ) + (a (n - 18) : ℤ) := by
  sorry

end OMA.S_oeis_a147792
