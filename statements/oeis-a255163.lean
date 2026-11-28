import Mathlib

/-!
# A255163: Irrational parts of circle radii in nested circles and hexagons (see comment).

Source: https://oeis.org/A255163
Credit: @agchua

Colin Barker (Feb 15 2015), in the formula section of A255163:
  Conjectures from Colin Barker, Feb 15 2015: (Start)
  a(n) = -12*a(n-1) + 12*a(n-2).
  G.f.: -(14*x+1) / (12*x^2-12*x-1). (End)
This file states both parts: the recurrence for n ≥ 2 (offset 0, so that all indices are terms),
and the g.f. as an identity of formal power series over ℚ,
(∑ a(n) X^n) * (12X^2 - 12X - 1) = -(14X + 1).
Definition: the comment of A255163 writes the radius of the n-th circle as R(n) = A(n) + B(n)*sqrt(3)
with A(0) = 2, A(n) = A255162(n), B(0) = 1 and B(n) = a(n). The entry's PARI program computes the
next radius by A(n+1) = 12*B(n) - 6*A(n), B(n+1) = 4*A(n) - 6*B(n) (that is,
R(n+1) = R(n)*(4*sqrt(3) - 6)) and prints the B(n); this rule is used as the definition below,
with the pair (A(n), B(n)) in ℤ × ℤ. It gives the listed terms 1, 2, -12, 168, -2160, ...
-/

namespace OMA.S_oeis_a255163

/-- The pair (A(n), B(n)) with R(n) = A(n) + B(n)*sqrt(3): (2, 1), then (A, B) ↦ (12B - 6A, 4A - 6B),
as in the entry's PARI program. -/
def AB : ℕ → ℤ × ℤ
  | 0 => (2, 1)
  | (n + 1) => (12 * (AB n).2 - 6 * (AB n).1, 4 * (AB n).1 - 6 * (AB n).2)

/-- A255163: a(n) = B(n), the irrational part of R(n). -/
def a (n : ℕ) : ℤ := (AB n).2

/-- Barker's conjectures: a(n) = -12a(n-1) + 12a(n-2) for n ≥ 2, and the g.f.
-(14x+1)/(12x^2-12x-1). -/
theorem main : (∀ n : ℕ, 2 ≤ n → a n = -12 * a (n - 1) + 12 * a (n - 2)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (12 * PowerSeries.X ^ 2 - 12 * PowerSeries.X - 1) =
      -(14 * PowerSeries.X + 1) := by
  sorry

end OMA.S_oeis_a255163
