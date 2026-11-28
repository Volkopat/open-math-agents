import Mathlib

/-!
OEIS A025165: a(n) = H_n(1) / 2^floor(n/2), offset zero, where H_n is the n-th
(physicists') Hermite polynomial: H_0 = 1, H_1 = 2x, H_{n+2} = 2x H_{n+1} - 2(n+1) H_n
(data: 1, 2, 1, -2, -5, -2, 23, ...).
Source: https://oeis.org/A025165
The conjecture is R. J. Mathar's recurrence (Feb 25 2015)
a(n) + a(n-1) + (2n-5) a(n-2) + (2n-7) a(n-3) + (n-2)(n-3) a(n-4) + (n-3)(n-4) a(n-5) = 0,
stated for n >= 5 so that every index is in the source domain. The quotient is taken in ℚ;
it is an integer, as in the source.
-/
namespace OMA.S_oeis_a025165

/-- `H_n(1)` for the physicists' Hermite polynomials. -/
def hermiteOne : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | (n + 2) => 2 * hermiteOne (n + 1) - 2 * ((n : ℤ) + 1) * hermiteOne n

/-- A025165: `a n = H_n(1) / 2^⌊n/2⌋`. -/
def a (n : ℕ) : ℚ := (hermiteOne n : ℚ) / 2 ^ (n / 2)

/-- Mathar's recurrence for A025165. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    a n + a (n - 1) + (2 * (n : ℚ) - 5) * a (n - 2) + (2 * (n : ℚ) - 7) * a (n - 3) +
      ((n : ℚ) - 2) * ((n : ℚ) - 3) * a (n - 4) + ((n : ℚ) - 3) * ((n : ℚ) - 4) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a025165
