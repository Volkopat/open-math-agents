import Mathlib

/-!
# A085614: Number of elementary arches of size n.

Source: https://oeis.org/A085614
Credit: @agchua

R. J. Mathar (Oct 18 2013), in the formula section of A085614:
  Conjecture: n*(n-1)*a(n) +(n-1)*(n-2)*a(n-1) -12*(3*n-5)*(3*n-7)*a(n-2) -12*(3*n-8)*(3*n-10)*a(n-3) = 0.
The entry has offset 1 (a(1) = 1, a(2) = 3, a(3) = 16, a(4) = 105; the g.f. is the series reversion
of x-3*x^2+2*x^3) and gives the closed form a(n) = 2^n*(3*n)!!/((n+1)!*n!!) (M. Krikun, May 25 2007).
That closed form is written with offset 0: at n = 0, 1, 2, 3 it gives 1, 3, 16, 105, the listed
terms a(1), a(2), a(3), a(4) (the same holds for the Gamma and Pochhammer forms of D. J. Jones).
In the offset of the entry it reads a(n) = 2^(n-1)*(3*(n-1))!!/(n!*(n-1)!!) for n >= 1, which is the
definition below (n!! is Nat.doubleFactorial n); it reproduces all listed data. The value at n = 0,
outside the offset, is never used. Mathar's recurrence is meant in the offset of the entry (with
the indexing of the closed form it already fails at n = 3). It uses a(n-3), so it is stated for
n >= 4. Values are taken in the rationals.
-/

namespace OMA.S_oeis_a085614

/-- A085614(n) = 2^(n-1) (3(n-1))!! / (n! (n-1)!!) for n >= 1 (Krikun's formula in the offset of the entry). -/
def a (n : ℕ) : ℚ :=
  2 ^ (n - 1) * (Nat.doubleFactorial (3 * (n - 1)) : ℚ)
    / ((n.factorial : ℚ) * (Nat.doubleFactorial (n - 1) : ℚ))

/-- Mathar's conjecture, for n >= 4:
n(n-1) a(n) + (n-1)(n-2) a(n-1) - 12(3n-5)(3n-7) a(n-2) - 12(3n-8)(3n-10) a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (n : ℚ) * ((n : ℚ) - 1) * a n + ((n : ℚ) - 1) * ((n : ℚ) - 2) * a (n - 1)
      - 12 * (3 * (n : ℚ) - 5) * (3 * (n : ℚ) - 7) * a (n - 2)
      - 12 * (3 * (n : ℚ) - 8) * (3 * (n : ℚ) - 10) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a085614
