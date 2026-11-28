import Mathlib

/-!
# A227720: Round(1/s(n)), where s(n) = n*log(1+1/n) - (2n-1)/(2n).

Source: https://oeis.org/A227720
Credit: @rickmanelius

Conjectures in the entry (Clark Kimberling, Jul 22 2013; the formula lines are unsigned):
a(n) = -2*a(n-1) - a(n-2) + a(n-4) - 2*a(n-5) + a(n-6) (conjectured).
G.f.: (-5 - 6 x - 7 x^2 - 5 x^3 - x^4)/((-1 + x)^3 (1 + x + x^2 + x^3)) (conjectured).
The comment adds: Conjecture: the four sequences are linearly recurrent. The four are A227719,
this sequence, A227721 and a sequence which possibly equals A094159; for this sequence that is
the recurrence and the g.f. above (the other entries are separate problems).

Formalization notes:
* Offset 1. `a n` is defined for every natural number n, but only a(1), a(2), ... enter the
  statement.
* s(n) is computed in the reals with `Real.log` of 1 + 1/n, exactly as in the name of the entry.
  Round is Mathlib's `round`, which rounds halves up, so `a n` is an integer. Mathematica's Round
  (the program in the entry) rounds halves to even; the two differ only at half-integers, and
  1/s(n) is never one for n ≥ 1 (it is irrational, because the logarithm of a rational number
  other than 1 is irrational).
* The recurrence line has a sign typo. As printed, with -2*a(n-1), it is false on the data of
  the entry: a(1), ..., a(7) = 5, 16, 34, 57, 86, 121, 163, but
  -2*121 - 86 + 34 - 2*16 + 5 = -321. The g.f. on the next line has the denominator
  (-1 + x)^3 (1 + x + x^2 + x^3) = -(1 - 2x + x^2 - x^4 + 2x^5 - x^6), whose recurrence is
  a(n) = 2*a(n-1) - a(n-2) + a(n-4) - 2*a(n-5) + a(n-6), and the data follow that one. So the
  recurrence is stated with +2*a(n-1), for n ≥ 7 (so that a(n-6) has index at least 1; the
  natural-number subtractions n - 1, ..., n - 6 are then exact).
* The g.f. has constant term (-5)/(-1) = 5 = a(1), so it is the series Sum_{m ≥ 0} a(m+1) x^m,
  written as `PowerSeries.mk` of m ↦ a(m+1). The identity is stated over ℤ⟦X⟧ with the
  denominator cleared (its constant coefficient is -1, a unit).
-/

namespace OMA.S_oeis_a227720

open PowerSeries

/-- s(n) = n*log(1+1/n) - (2n-1)/(2n), in the reals. -/
noncomputable def s (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (1 + 1 / (n : ℝ)) - (2 * (n : ℝ) - 1) / (2 * (n : ℝ))

/-- A227720: a(n) = Round(1/s(n)). -/
noncomputable def a (n : ℕ) : ℤ := round (1 / s n)

/-- Kimberling's conjectures on A227720: the linear recurrence of order 6 (with the sign given by
its g.f.) for n ≥ 7, and the g.f.
(-5 - 6x - 7x^2 - 5x^3 - x^4)/((-1 + x)^3 (1 + x + x^2 + x^3)) of a(1), a(2), ...,
with the denominator cleared. -/
theorem main :
    (∀ n : ℕ, 7 ≤ n →
      a n = 2 * a (n - 1) - a (n - 2) + a (n - 4) - 2 * a (n - 5) + a (n - 6)) ∧
    PowerSeries.mk (fun m => a (m + 1)) *
        ((-1 + X) ^ 3 * (1 + X + X ^ 2 + X ^ 3) : PowerSeries ℤ) =
      -5 - 6 * X - 7 * X ^ 2 - 5 * X ^ 3 - X ^ 4 := by
  sorry

end OMA.S_oeis_a227720
