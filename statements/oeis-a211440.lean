import Mathlib

/-!
# A211440: Number of ordered triples (w,x,y) with all terms in {-n,...,0,...,n} and 2w+3x+3y=0.

Source: https://oeis.org/A211440
Credit: @agchua

Colin Barker (May 15 2017), in the formula section of A211440:
  Conjectures from Colin Barker, May 15 2017: (Start)
  G.f.: (1 + 3*x + x^2)*(1 - x + 4*x^2 - x^3 + x^4) / ((1 - x)^3*(1 + x + x^2)^2).
  a(n) = a(n-1) + 2*a(n-3) - 2*a(n-4) - a(n-6) + a(n-7) for n>6.
  (End)
This file states both parts: the recurrence for n > 6 as written (offset 0, so every index is a
term), and the g.f. as an identity of formal power series over ℚ,
(∑ a(n) X^n) * ((1 - X)^3 (1 + X + X^2)^2) = (1 + 3X + X^2)(1 - X + 4X^2 - X^3 + X^4).
(The entry also lists, from Robert Israel, Apr 03 2019, a closed form of a(n) by n mod 3, without
proof.) The triples are taken in ℤ × ℤ × ℤ, each entry in Finset.Icc (-n) n. The definition is
marked noncomputable because Finset.Icc on ℤ is elaborated through a noncomputable order instance.
-/

namespace OMA.S_oeis_a211440

/-- A211440(n): the number of triples (w, x, y) in {-n, ..., n}^3 with 2w + 3x + 3y = 0. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun t : ℤ × ℤ × ℤ => 2 * t.1 + 3 * t.2.1 + 3 * t.2.2 = 0)).card

/-- Barker's conjectures: the recurrence for n > 6 and the generating function. -/
theorem main : (∀ n : ℕ, 6 < n →
      (a n : ℤ) = (a (n - 1) : ℤ) + 2 * (a (n - 3) : ℤ) - 2 * (a (n - 4) : ℤ)
        - (a (n - 6) : ℤ) + (a (n - 7) : ℤ)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 2) =
      (1 + 3 * PowerSeries.X + PowerSeries.X ^ 2) *
        (1 - PowerSeries.X + 4 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 4) := by
  sorry

end OMA.S_oeis_a211440
