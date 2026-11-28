import Mathlib

/-!
# A267068: a(n) = (n+1) / A189733(n).

Source: https://oeis.org/A267068
Credit: @rtflynn (agent: Claude Code, model claude-opus-5-5)

The entry (offset 0, data 1, 2, 3, 2, 5, 1, 7, 2, 3, 2, 11, 1, ...) records in its FORMULA section
(Colin Barker, Jan 10 2016):

  Conjectures: a(n) = 2*a(n-6) - a(n-12) for n>11.
  G.f.: (1+2*x+3*x^2+2*x^3+5*x^4+x^5+5*x^6-2*x^7-3*x^8-2*x^9+x^10-x^11) /
        ((1-x)^2*(1+x)^2*(1-x+x^2)^2*(1+x+x^2)^2).

Definitions, following A189733: A189733(n) is the denominator of `B(0,n)`, where the array of
fractions `B(m,n)` (`0 ≤ m ≤ n`) is given by `B(n,n) = 0`, `B(n-1,n) = (-1)^(n+1)/n` and
`B(m,n) = B(m+1,n-1) + B(m,n-1)`. Only the entries with `m ≤ n` are used to compute `B(0,n)`
(the Mathematica program of the entry also fills `m > n`, by the same recurrence solved for the
other entry, but those entries never enter `B(0,n)`).
* `c m d = B(m, m+d)`: `c m 0 = B(m,m) = 0`, `c m 1 = B(m,m+1) = (-1)^(m+2)/(m+1)`, and for
  `d ≥ 0`, `c m (d+2) = B(m,m+d+2) = B(m+1,m+d+1) + B(m,m+d+1) = c (m+1) d + c m (d+1)`.
* `A189733 n` is the denominator of the rational `B(0,n) = c 0 n` (in lowest terms,
  `Rat.den`; the denominator of 0 is 1, as in the data a(0) = 1).
* `a n = (n+1) / A189733 n`, taken in `ℚ` so that no divisibility is assumed.
* The denominator of the g.f. is `(1-x)^2 (1+x)^2 (1-x+x^2)^2 (1+x+x^2)^2`, stated as written;
  the g.f. is the formal power series `∑_{n ≥ 0} a(n) x^n` over `ℚ`, and the claim is written as
  `(∑ a(n) x^n) * denominator = numerator`.
Both conjectures are stated, as a conjunction.
-/

namespace OMA.S_oeis_a267068

/-- `c m d = B(m, m+d)`. -/
def c : ℕ → ℕ → ℚ
  | _, 0 => 0
  | m, 1 => (-1) ^ (m + 2) / (m + 1)
  | m, d + 2 => c (m + 1) d + c m (d + 1)

/-- `B(m, n)` for `m ≤ n`. -/
def B (m n : ℕ) : ℚ := c m (n - m)

/-- A189733(n): the denominator of `B(0, n)`. -/
def A189733 (n : ℕ) : ℕ := (B 0 n).den

/-- A267068(n) = (n+1) / A189733(n). -/
def a (n : ℕ) : ℚ := ((n + 1 : ℕ) : ℚ) / (A189733 n : ℚ)

/-- Both conjectures of the entry: the recurrence and the rational generating function. -/
theorem main :
    (∀ n, 11 < n → a n = 2 * a (n - 6) - a (n - 12)) ∧
      PowerSeries.mk a *
          ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 *
            (1 - PowerSeries.X + PowerSeries.X ^ 2) ^ 2 *
            (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 2) =
        1 + 2 * PowerSeries.X + 3 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 +
          5 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5 + 5 * PowerSeries.X ^ 6 -
          2 * PowerSeries.X ^ 7 - 3 * PowerSeries.X ^ 8 - 2 * PowerSeries.X ^ 9 +
          PowerSeries.X ^ 10 - PowerSeries.X ^ 11 := by
  sorry

end OMA.S_oeis_a267068
