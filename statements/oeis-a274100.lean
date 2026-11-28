import Mathlib

/-!
# A274100: Barker's recurrence

Source: https://oeis.org/A274100
Credit: @ivillar

The number of partitions of 2^n into at most four parts, i.e. the coefficient of x^(2^n) in
1/((1-x)*(1-x^2)*(1-x^3)*(1-x^4)) (offset 0; data 1, 2, 5, 15, 64, 351, 2280, ...). Colin Barker
conjectured (Jun 12 2016) a(n) = 14*a(n-1) - 55*a(n-2) + 50*a(n-3) + 56*a(n-4) - 64*a(n-5)
for n > 6.

Status: conjecture recorded in the entry (Colin Barker, Jun 12 2016).

Formalization notes:
* A partition of N into at most four parts is written N = a + b + c + d with a >= b >= c >= d >= 0
  (padding with zero parts); it is determined by d in [0, floor(N/4)], c in [d, floor((N - d)/3)]
  and b in [c, floor((N - c - d)/2)], and `a` counts these triples for N = 2^n.
* The recurrence is stated over ℤ.
* Barker's generating function (1-12*x+32*x^2+5*x^3-27*x^4-18*x^5-16*x^6) /
  ((1-x)*(1+x)*(1-2*x)*(1-4*x)*(1-8*x)) is the rational function determined by the recurrence and
  the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a274100

/-- A274100: the number of partitions `2^n = a + b + c + d` with `a ≥ b ≥ c ≥ d ≥ 0`. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.range (2 ^ n / 4 + 1), ∑ c ∈ Finset.Icc d ((2 ^ n - d) / 3),
    ∑ _b ∈ Finset.Icc c ((2 ^ n - c - d) / 2), 1

/-- Barker's conjectured recurrence for A274100, for every `n > 6`. -/
theorem main : ∀ n : ℕ, 6 < n →
    (a n : ℤ) = 14 * a (n - 1) - 55 * a (n - 2) + 50 * a (n - 3) + 56 * a (n - 4) -
      64 * a (n - 5) := by
  sorry

end OMA.S_oeis_a274100
