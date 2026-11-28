import Mathlib

/-!
# A331944: a(n)/ceiling(6^(n-7)) is the expected number of rolls of a fair 6-sided die in a game where the player starts at 0, advances the position by the outcome of the die's roll until exactly position n is reached. Positions beyond n are avoided by staying at the last visited position, but counting the rolls.

Source: https://oeis.org/A331944
Credit: @agchua

Colin Barker, in the formula section of A331944:
  Conjectures from _Colin Barker_, Feb 21 2020: (Start)
  G.f.: x*(6 - 36*x - 36*x^2 - 36*x^3 - 36*x^4 - 36*x^5 - 35*x^6 + 279930*x^7 + 279900*x^8 + 279720*x^9 + 278640*x^10 + 272160*x^11 + 233280*x^12) / ((1 - 6*x)^2*(1 + 5*x + 24*x^2 + 108*x^3 + 432*x^4 + 1296*x^5)).
  a(n) = 7*a(n-1) - 46656*a(n-7) for n>13.
  (End)
This file states both parts: the g.f. as an identity of formal power series over ℚ for the series
Σ_{n ≥ 1} a(n) x^n (offset 1, so the coefficient of x^0 is 0), and the recurrence for n ≥ 14.

The expected number of rolls. Let E(d) be the expected number of further rolls when the target is
d positions ahead; the game of the entry starts at 0 with target n, so its expected length is
E(n). A roll k in 1..6 (each with probability 1/6) moves to distance d - k if k ≤ d and keeps the
position if k > d, and every roll counts. First-step analysis gives E(0) = 0 and, for d ≥ 1,
  E(d) = 1 + (1/6) * Σ_{k=1..6} (E(d-k) if k ≤ d, and E(d) if k > d).
With m = min(d, 6) this reads (m/6) * E(d) = 1 + (1/6) * Σ_{k=1..m} E(d-k), that is
  E(d) = (6 + Σ_{k=1..m} E(d-k)) / m,
which is the recursion that defines E below (for the distance d + 1, the summand with index k in
range 6 is the roll k + 1). This is the linear system that the entry's PARI program solves with
the fundamental matrix (1 - M/6)^(-1); the definition reproduces all listed terms. Then
a(n) = E(n) * ceiling(6^(n-7)), with 6^(n-7) computed in ℚ, so that the factor is 1 for n ≤ 7.
-/

namespace OMA.S_oeis_a331944

/-- E(d): the expected number of rolls needed to reach the target exactly from d positions before
it: E(0) = 0 and E(d) = (6 + Σ_{k=1..min(d,6)} E(d-k)) / min(d,6) for d ≥ 1. -/
noncomputable def E : ℕ → ℚ
  | 0 => 0
  | d + 1 => (6 + ∑ k ∈ Finset.range 6, if k + 1 ≤ d + 1 then E (d - k) else 0) /
      ((min (d + 1) 6 : ℕ) : ℚ)

/-- a(n) = E(n) * ceiling(6^(n-7)). -/
noncomputable def a (n : ℕ) : ℚ := E n * (⌈(6 : ℚ) ^ ((n : ℤ) - 7)⌉ : ℚ)

/-- Barker's conjectures: the g.f. x*(6 - 36*x - 36*x^2 - 36*x^3 - 36*x^4 - 36*x^5 - 35*x^6 +
279930*x^7 + 279900*x^8 + 279720*x^9 + 278640*x^10 + 272160*x^11 + 233280*x^12) /
((1 - 6*x)^2*(1 + 5*x + 24*x^2 + 108*x^3 + 432*x^4 + 1296*x^5)), and
a(n) = 7*a(n-1) - 46656*a(n-7) for n > 13. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) *
        ((1 - 6 * PowerSeries.X) ^ 2 *
          (1 + 5 * PowerSeries.X + 24 * PowerSeries.X ^ 2 + 108 * PowerSeries.X ^ 3 +
            432 * PowerSeries.X ^ 4 + 1296 * PowerSeries.X ^ 5)) =
      PowerSeries.X * (6 - 36 * PowerSeries.X - 36 * PowerSeries.X ^ 2 - 36 * PowerSeries.X ^ 3 -
        36 * PowerSeries.X ^ 4 - 36 * PowerSeries.X ^ 5 - 35 * PowerSeries.X ^ 6 +
        279930 * PowerSeries.X ^ 7 + 279900 * PowerSeries.X ^ 8 + 279720 * PowerSeries.X ^ 9 +
        278640 * PowerSeries.X ^ 10 + 272160 * PowerSeries.X ^ 11 + 233280 * PowerSeries.X ^ 12) ∧
    ∀ n : ℕ, 14 ≤ n → a n = 7 * a (n - 1) - 46656 * a (n - 7) := by
  sorry

end OMA.S_oeis_a331944