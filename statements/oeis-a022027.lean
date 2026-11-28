import Mathlib

/-!
# A022027: Define the sequence T(a(0),a(1)) by a(n+2) is the greatest integer such that a(n+2)/a(n+1) < a(n+1)/a(n) for n >= 0. This is T(2,16).

Source: https://oeis.org/A022027
Credit: @agchua

Colin Barker (Sep 18 2015), in the formula section of A022027:
  Conjectures: a(n) = 8*a(n-1)-4*a(n-3). G.f.: -(x^2-2) / (4*x^3-8*x+1).
This file states both parts: the recurrence for n ≥ 3 (offset 0, so that all indices are terms),
and the g.f. as an identity of formal power series over ℚ, (∑ a(n) X^n) * (4X^3 - 8X + 1) =
-(X^2 - 2).
Definition: a(0) = 2, a(1) = 16. All terms are positive, and for positive a(n), a(n+1) the condition
k/a(n+1) < a(n+1)/a(n) says k < a(n+1)^2/a(n), whose greatest integer solution is
ceiling(a(n+1)^2/a(n)) - 1. This is the formula a(n+1) = ceiling(a(n)^2/a(n-1))-1 of M. F. Hasler
(Feb 11 2016) in the same entry and the rule of the entry's PARI and Magma programs; it is used as
the definition below, with the quotient taken in ℚ and Int.ceil.
-/

namespace OMA.S_oeis_a022027

/-- A022027: a(0) = 2, a(1) = 16, a(n+2) = ceiling(a(n+1)^2/a(n)) - 1. -/
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 16
  | (n + 2) => ⌈((a (n + 1) : ℚ) ^ 2 / (a n : ℚ))⌉ - 1

/-- Barker's conjectures: the recurrence a(n) = 8a(n-1) - 4a(n-3) for n ≥ 3, and the g.f.
-(x^2-2)/(4x^3-8x+1). -/
theorem main : (∀ n : ℕ, 3 ≤ n → a n = 8 * a (n - 1) - 4 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (4 * PowerSeries.X ^ 3 - 8 * PowerSeries.X + 1) =
      -(PowerSeries.X ^ 2 - 2) := by
  sorry

end OMA.S_oeis_a022027
