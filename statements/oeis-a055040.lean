import Mathlib

/-!
# A055040: Numbers of the form 3^(2i+1)*(3j+2)

Source: https://oeis.org/A055040
Credit: @jagong-cmu

THE CONJECTURE AS STATED IS FALSE. It fails at the coefficient of x^1: the conjectured
g.f. has x-coefficient 2, but a(1) = 6.

The entry has the formula line
G.f.: [x(x+2)(x^2+x+1)(x^7+x^3+1)]/(x^11-x^10-x+1) (conjectured).
This file states that line exactly as written, so that it can be refuted.
The expansion of the conjectured g.f. is 2x + 5x^2 + 8x^3 + 11x^4 + ..., while the data
is 6, 15, 24, 33, .... (The expansion matches A055048 = A055040/3 at first; even three
times the g.f. fails, first at n = 61, where a(61) = 486 = 3^5 * 2 but the coefficient is 492.)

Conventions:
* `IsTerm m` means `m = 3^(2i+1) * (3j+2)` for some `i, j ≥ 0`, as in the OEIS name.
* Offset 1: `a n = Nat.nth IsTerm (n - 1)` is the `n`-th term in increasing order, for `n ≥ 1`.
* The g.f. is `A = Sum_{n ≥ 1} a(n) x^n` in `PowerSeries ℤ` (coefficient `0` at `x^0`), and the
  conjecture is stated with the denominator cleared:
  `A * (x^11 - x^10 - x + 1) = x (x + 2) (x^2 + x + 1) (x^7 + x^3 + 1)`.
  The denominator has constant term `1`, so it is a unit and this is equivalent to the quotient form.
-/

namespace OMA.S_oeis_a055040

/-- `m` is of the form `3^(2i+1) * (3j+2)`. -/
def IsTerm (m : ℕ) : Prop := ∃ i j : ℕ, m = 3 ^ (2 * i + 1) * (3 * j + 2)

/-- The `n`-th term of A055040 (offset 1): the `n`-th number of the form `3^(2i+1)*(3j+2)`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- The ordinary generating function `Sum_{n ≥ 1} a(n) x^n`. -/
noncomputable def A : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℤ)

/-- The conjectured g.f. `x(x+2)(x^2+x+1)(x^7+x^3+1)/(x^11-x^10-x+1)`, as written in OEIS.
It is false (the coefficient of `x^1` is `2`, but `a(1) = 6`). -/
theorem main :
    A * ((PowerSeries.X : PowerSeries ℤ) ^ 11 - PowerSeries.X ^ 10 - PowerSeries.X + 1) =
      PowerSeries.X * (PowerSeries.X + 2) * (PowerSeries.X ^ 2 + PowerSeries.X + 1) *
        (PowerSeries.X ^ 7 + PowerSeries.X ^ 3 + 1) := by
  sorry

end OMA.S_oeis_a055040
