import Mathlib

/-!
# A007901: a conjectured recurrence for minimal unavoidable pebbling configurations

Source: https://oeis.org/A007901
Credit: @sntntHb

`a(n)` (offset 1) is the number of minimal unavoidable `n`-celled pebbling configurations, with
generating function (from the Stanley reference, as recorded by Joerg Arndt)
`x^3 ((1 - 3x + x^2) sqrt(1 - 4x) - 1 + 5x - x^2 - 6x^3) / (1 - 7x + 14x^2 - 9x^3)`.
The entry records the conjecture (R. J. Mathar, Aug 14 2012)
`(n-3)(n-8) a(n) + (-11n^2 + 127n - 324) a(n-1) + 42(n^2 - 12n + 34) a(n-2)
 + (-65n^2 + 799n - 2400) a(n-3) + 18(n-6)(2n-13) a(n-4) = 0`.

The sequence is defined here from the generating function. The coefficients of `sqrt(1 - 4x)`
are `1` and `-2 C(m-1)` for `m ≥ 1`, with `C` the Catalan numbers; `e m` is the `m`-th coefficient
of `(1 - 3x + x^2) sqrt(1 - 4x) - 1 + 5x - x^2 - 6x^3`, and multiplying out the denominator gives
`a(n) = e(n-3) + 7 a(n-1) - 14 a(n-2) + 9 a(n-3)` with `a(n) = 0` for `n ≤ 0`. This reproduces the
listed data `0, 0, 0, 0, 4, 22, 98, 412, 1700, 6974, ...` for `n = 1, 2, 3, ...`.

With these values the recurrence holds for every `n ≥ 8` (checked numerically up to `n = 200`)
and fails for `n = 5, 6, 7`, where the initial terms of the generating function do not yet
follow it; the conjecture is stated for `n ≥ 8`.
-/

namespace OMA.S_oeis_a007901

/-- Coefficients of `sqrt(1 - 4x)`: `1`, then `-2 C(m-1)`. -/
def s (m : ℕ) : ℤ := if m = 0 then 1 else -2 * (catalan (m - 1) : ℤ)

/-- Coefficients of `(1 - 3x + x^2) sqrt(1 - 4x) - 1 + 5x - x^2 - 6x^3`. -/
def e (m : ℕ) : ℤ :=
  s m - (if 1 ≤ m then 3 * s (m - 1) else 0) + (if 2 ≤ m then s (m - 2) else 0) +
    (if m = 0 then -1 else if m = 1 then 5 else if m = 2 then -1 else if m = 3 then -6 else 0)

/-- OEIS A007901 (offset 1), indexed by all naturals with `a 0 = 0`; the coefficients of the
generating function above. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | n + 4 => e (n + 1) + 7 * a (n + 3) - 14 * a (n + 2) + 9 * a (n + 1)

/-- Mathar's conjectured recurrence for A007901, for `n ≥ 8`. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    ((n : ℤ) - 3) * ((n : ℤ) - 8) * a n + (-11 * (n : ℤ) ^ 2 + 127 * n - 324) * a (n - 1) +
      42 * ((n : ℤ) ^ 2 - 12 * n + 34) * a (n - 2) +
      (-65 * (n : ℤ) ^ 2 + 799 * n - 2400) * a (n - 3) +
      18 * ((n : ℤ) - 6) * (2 * (n : ℤ) - 13) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a007901
