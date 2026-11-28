import Mathlib

/-!
# A025245: a(n) = (1/2)*s(n+3), where s = A025244.

Source: https://oeis.org/A025245
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A025245 (R. J. Mathar, Feb 25 2015):
(n+3)*a(n) +(-2*n-3)*a(n-1) -n*a(n-2) +3*(-2*n+3)*a(n-3) +(n-3)*a(n-4)=0.

Conventions:
* s = A025244 has offset 1 and is defined in its entry by
  s(n) = s(1)*s(n-1) + s(2)*s(n-2) + ... + s(n-3)*s(3) for n >= 4, with initial terms
  1, 1, 2, 2 (data 1, 1, 2, 2, 4, 10, 22, 52, 130, ...). The sum is
  Sum_{k=1..n-3} s(k)*s(n-k), the sum over `Finset.Icc 1 (n - 3)`. The fourth initial term
  s(4) = 2 is also the value given by the recurrence at n = 4 (s(1)*s(3) = 2), so only
  s(1) = 1, s(2) = 1, s(3) = 2 are assumed. The statement is made for every integer sequence
  `s : ℕ → ℤ` satisfying these conditions (the value `s 0` is not used); the terms s(n) with
  n >= 1 are determined by them, so this is the same as making it for A025244.
* A025245 has offset 1 and a(n) = (1/2)*s(n+3) (data 1, 2, 5, 11, 26, 65, 163, ...); it is
  `a s n` below, a rational number (in fact an integer).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 5`, which is
  exactly the range in which all the indices n, n-1, ..., n-4 are at least the offset 1.
* The identity is stated in `ℚ`, with the natural number `n` cast to `ℚ`, so the polynomial
  coefficients with negative values are exact.
-/

namespace OMA.S_oeis_a025245

/-- a(n) = (1/2)*s(n+3). -/
def a (s : ℕ → ℤ) (n : ℕ) : ℚ := (s (n + 3) : ℚ) / 2

/-- For every `n ≥ 5`,
(n+3)*a(n) + (-2*n-3)*a(n-1) - n*a(n-2) + 3*(-2*n+3)*a(n-3) + (n-3)*a(n-4) = 0. -/
theorem main : ∀ s : ℕ → ℤ, s 1 = 1 → s 2 = 1 → s 3 = 2 →
    (∀ n : ℕ, 4 ≤ n → s n = ∑ k ∈ Finset.Icc 1 (n - 3), s k * s (n - k)) →
    ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) + 3) * a s n + (-2 * (n : ℚ) - 3) * a s (n - 1) - (n : ℚ) * a s (n - 2)
      + 3 * (-2 * (n : ℚ) + 3) * a s (n - 3) + ((n : ℚ) - 3) * a s (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a025245
