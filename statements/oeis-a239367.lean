import Mathlib

/-!
# A239367: the odd-indexed bisection of A238315

Source: https://oeis.org/A239367 (conjectures by Colin Barker, Dec 30 2014)

Entry (offset 1): The bisection of A238315 that remains constant with changes in the offset of
the exponent of the second term. Here A238315 (offset 1) is the oscillating sequence
`b(1) = 1`, `b(n) = n^2 + 2^(n-1) - 2*b(n-1)` for `n > 1`; the bisection that stays constant is
the one at odd indices (the entry's comment and data: 1, 5, 13, 29, 69, ... are
b(1), b(3), b(5), b(7), b(9), ...), so `a(n) = b(2*n - 1)` for `n >= 1`.
Formula section, Conjectures from Colin Barker, Dec 30 2014:
a(n) = (-1+4^n-12*n+36*n^2)/27.
a(n) = 6*a(n-1)-8*a(n-2)-2*a(n-3)+9*a(n-4)-4*a(n-5).
G.f.: -x*(7*x^2+2*x-1) / ((x-1)^3*(4*x-1)).

Formalization notes:
* Values are taken in `ℤ`. The index 0 lies outside both offsets: `b 0` and `a 0` are junk values
  (`b 0 = 0`) that are never used by the statement.
* The closed form is stated for `n >= 1` after multiplying both sides by 27.
* The recurrence has no stated range; it is stated for `n >= 6`, the range where all five
  earlier indices are at least the offset 1.
* With offset 1 the generating function is `A(x) = Sum_(n >= 1) a(n) x^n`, the power series with
  coefficient 0 at `x^0`. Since `(x-1)^3*(4*x-1)` has constant term 1, the identity `A = N/D` is
  stated as `A * D = N` in the formal power series ring over the integers.
* Controls from the entry: a(1..6) = 1, 5, 13, 29, 69, 197.
-/

namespace OMA.S_oeis_a239367

open PowerSeries

/-- A238315 (offset 1): `b(1) = 1`, `b(n) = n^2 + 2^(n-1) - 2*b(n-1)`; `b 0 = 0` is a junk value. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => ((n : ℤ) + 2) ^ 2 + 2 ^ (n + 1) - 2 * b (n + 1)

/-- A239367(n) = A238315(2n-1) for `n >= 1`. -/
def a (n : ℕ) : ℤ := b (2 * n - 1)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → 27 * a n = -1 + 4 ^ n - 12 * n + 36 * (n : ℤ) ^ 2) ∧
    (∀ n : ℕ, 6 ≤ n →
      a n = 6 * a (n - 1) - 8 * a (n - 2) - 2 * a (n - 3) + 9 * a (n - 4) - 4 * a (n - 5)) ∧
    mk (fun n => if n = 0 then 0 else a n) * ((X - 1) ^ 3 * (4 * X - 1)) =
      (-X * (7 * X ^ 2 + 2 * X - 1) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a239367
