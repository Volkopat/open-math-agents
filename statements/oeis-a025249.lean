import Mathlib

/-!
# A025249: a(n) = (1/2)*s(n+3), where s = A025248.

Source: https://oeis.org/A025249
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A025249 (R. J. Mathar, Feb 25 2015):
+(n+3)*a(n) +(-2*n-3)*a(n-1) +n*a(n-2) +4*(-2*n+3)*a(n-3)=0.

Conventions:
* s = A025248 has offset 1 and is defined in its entry by
  s(n) = s(1)*s(n-1) + s(2)*s(n-2) + ... + s(n-3)*s(3) for n >= 4, with initial terms
  1, 0, 2, 2 (data 1, 0, 2, 2, 2, 6, 14, 26, 58, ...). The sum is
  Sum_{k=1..n-3} s(k)*s(n-k), the sum over `Finset.Icc 1 (n - 3)`. The fourth initial term
  s(4) = 2 is also the value given by the recurrence at n = 4 (s(1)*s(3) = 2), so only
  s(1) = 1, s(2) = 0, s(3) = 2 are assumed. The statement is made for every integer sequence
  `s : ℕ → ℤ` satisfying these conditions (the value `s 0` is not used); the terms s(n) with
  n >= 1 are determined by them, so this is the same as making it for A025248.
* A025249 has offset 1 and a(n) = (1/2)*s(n+3) (data 1, 1, 3, 7, 13, 29, 71, ...); it is
  `a s n` below, a rational number (in fact an integer).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 4`, which is
  exactly the range in which all the indices n, n-1, n-2, n-3 are at least the offset 1.
* The identity is stated in `ℚ`, with the natural number `n` cast to `ℚ`, so the polynomial
  coefficients with negative values are exact.
-/

namespace OMA.S_oeis_a025249

/-- a(n) = (1/2)*s(n+3). -/
def a (s : ℕ → ℤ) (n : ℕ) : ℚ := (s (n + 3) : ℚ) / 2

/-- For every `n ≥ 4`, (n+3)*a(n) + (-2*n-3)*a(n-1) + n*a(n-2) + 4*(-2*n+3)*a(n-3) = 0. -/
theorem main : ∀ s : ℕ → ℤ, s 1 = 1 → s 2 = 0 → s 3 = 2 →
    (∀ n : ℕ, 4 ≤ n → s n = ∑ k ∈ Finset.Icc 1 (n - 3), s k * s (n - k)) →
    ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 3) * a s n + (-2 * (n : ℚ) - 3) * a s (n - 1) + (n : ℚ) * a s (n - 2)
      + 4 * (-2 * (n : ℚ) + 3) * a s (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a025249
