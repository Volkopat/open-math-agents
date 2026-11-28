import Mathlib

/-!
# A200039: Number of -n..n arrays x(0..2) of 3 elements with sum zero and with zeroth through 2nd differences all nonzero.

Source: https://oeis.org/A200039
Credit: @agchua

Colin Barker (May 17 2018), in the formula section of A200039:
  Conjectures from Colin Barker, May 17 2018: (Start)
  G.f.: 2*x^2*(1 + 5*x) / ((1 - x)^3*(1 + x)).
  a(n) = -5*n + 3*n^2 for n even.
  a(n) = 2 - 5*n + 3*n^2 for n odd.
  (End)
This file states all three. The offset is 1, so the g.f. is the series sum over n >= 1 of
a(n) x^n, written as X * mk (fun n => a (n + 1)) and stated as an identity of formal power
series over Q; the two closed forms are stated in Z for n >= 1.
Definition: an array x(0..2) is a triple (x(0), x(1), x(2)) of integers in [-n, n]. Its zeroth
differences are x(0), x(1), x(2), its first differences are x(1) - x(0) and x(2) - x(1), and its
second difference is x(2) - 2 x(1) + x(0). a(n) counts the arrays with x(0) + x(1) + x(2) = 0
whose six differences are all nonzero. This gives the listed terms 0, 2, 14, 28, 52, 78, ...
-/

namespace OMA.S_oeis_a200039

/-- The arrays counted by A200039(n), as triples (x(0), x(1), x(2)). -/
noncomputable def goodSet (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun x => x.1 + x.2.1 + x.2.2 = 0 ∧ x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.2.2 ≠ 0 ∧
      x.2.1 - x.1 ≠ 0 ∧ x.2.2 - x.2.1 ≠ 0 ∧ x.2.2 - 2 * x.2.1 + x.1 ≠ 0)

/-- A200039(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (goodSet n).card

/-- Barker's conjectures: the g.f. 2x^2(1 + 5x)/((1 - x)^3(1 + x)), a(n) = -5n + 3n^2 for even n,
and a(n) = 2 - 5n + 3n^2 for odd n. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X)) =
      2 * PowerSeries.X ^ 2 * (1 + 5 * PowerSeries.X) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℤ) = -5 * n + 3 * n ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℤ) = 2 - 5 * n + 3 * n ^ 2) := by
  sorry

end OMA.S_oeis_a200039
