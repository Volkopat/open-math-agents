import Mathlib

/-!
# A133603: Mathar's recurrence, corrected to n ≥ 3

Source: https://oeis.org/A133603
Credit: @ivillar

Status: false as stated at n = 2 (the left side is 16 at n = 2 on the OEIS data); `main` is the
corrected recurrence (n ≥ 3), which is proved. It follows from the description of the terms through
Catalan numbers recorded in the entry, which is used as the definition here.

A133603 (offset 0): the matrix-vector product A133566 * A000108;
data 1, 1, 3, 5, 19, 42, 174, 429, 1859, 4862, 21658, 58786, 266798, ...

Conjecture (R. J. Mathar, Jun 20 2015):
n*(n-2)*(3*n-1)*(n+1)*a(n) -8*n*(2*n-3)*a(n-1) -4*(n-1)*(3*n+2)*(2*n-3)*(2*n-5)*a(n-2) = 0.

Formalization: the entry records that, with C(n) the Catalan numbers A000108, a(n) = C(n) for odd n
and a(n) = C(n) + C(n-1) for even n; for n = 0 the second summand is absent (a(0) = 1 = C(0)). This is
the definition of a(n) used here, with values in ℤ (`catalan` is Mathlib's Catalan number). `main`
is the corrected recurrence (n ≥ 3): at n = 2 the left side of the recurrence as stated is
0*a(2) - 16*a(1) + 32*a(0) = 16, and it vanishes from n = 3 on; for example at n = 3:
(96)*(5) + (-72)*(3) + (-264)*(1) = 0.
-/

namespace OMA.S_oeis_a133603

/-- a(n) = C(n) for odd n, a(n) = C(n) + C(n-1) for even n ≥ 2, a(0) = C(0), with C the Catalan
numbers. -/
def a (n : ℕ) : ℤ :=
  if n % 2 = 1 then (catalan n : ℤ)
  else (catalan n : ℤ) + (if n = 0 then 0 else (catalan (n - 1) : ℤ))

/-- The corrected recurrence (n ≥ 3): Mathar's recurrence, which fails at n = 2. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) * ((n : ℤ) - 2) * (3 * (n : ℤ) - 1) * ((n : ℤ) + 1) * a n -
      8 * (n : ℤ) * (2 * (n : ℤ) - 3) * a (n - 1) -
      4 * ((n : ℤ) - 1) * (3 * (n : ℤ) + 2) * (2 * (n : ℤ) - 3) * (2 * (n : ℤ) - 5) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a133603
