import Mathlib

/-!
# A010905: the linear recurrence of the Pisot sequence E(4,15)

Source: https://oeis.org/A010905
Credit: @ivillar

A010905 (offset 0) is the Pisot sequence E(4,15): a(0) = 4, a(1) = 15, and
a(n) = floor(a(n-1)^2/a(n-2) + 1/2) for n > 1; data 4, 15, 56, 209, 780, 2911, ...
The formula a(n) = 4*a(n-1) - a(n-2) for n >= 2 was conjectured by Colin Barker (Apr 16 2012);
it implies the g.f. (4-x)/(1-4*x+x^2). N. J. A. Sloane (Sep 09 2016) records a proof using the
PtoRv program of Ekhad, Sloane and Zeilberger.

Formalization: the quotient a(n-1)^2/a(n-2) + 1/2 is computed in ℚ and `⌊·⌋` is the floor;
the terms are integers. The recurrence is stated for every n ≥ 2.
-/

namespace OMA.S_oeis_a010905

/-- The Pisot sequence E(4,15): a(0) = 4, a(1) = 15, a(n) = floor(a(n-1)^2/a(n-2) + 1/2). -/
def a : ℕ → ℤ
  | 0 => 4
  | 1 => 15
  | n + 2 => ⌊((a (n + 1) : ℚ) ^ 2 / (a n : ℚ) + 1 / 2)⌋

/-- Barker's conjecture: a(n) = 4*a(n-1) - a(n-2) for n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n = 4 * a (n - 1) - a (n - 2) := by
  sorry

end OMA.S_oeis_a010905
