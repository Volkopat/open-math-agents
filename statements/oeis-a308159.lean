import Mathlib

/-!
# OEIS A308159: Barker's generating function and recurrence

Source: https://oeis.org/A308159 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Wesley Ivan Hurt, May 14 2019), offset 1: Sum of the largest sides of all integer-sided
isosceles triangles with perimeter n. Data: 0, 0, 1, 0, 2, 2, 6, 3, 7, 8, 14, 9, 16, ...
Formula lines: Conjectures from Colin Barker, May 15 2019:
G.f.: x^3*(1 + 2*x^2 + x^3 + 4*x^4 + x^5 + x^6) / ((1 - x)^3*(1 + x)^2*(1 + x^2)^2*(1 + x + x^2)).
a(n) = a(n-3) + 2*a(n-4) - 2*a(n-7) - a(n-8) + a(n-11) for n>11.

Formalization notes:
* An integer-sided triangle with perimeter n is a triple of positive integers x <= y <= z with
  x + y + z = n and z < x + y (nondegenerate); it is isosceles when x = y or y = z (equilateral
  triangles included once). Its largest side is z. This is Hurt's double-sum formula in the
  entry, and it reproduces the data.
* The generating function is the formal power series sum_{n >= 0} a(n) x^n over the rationals
  (a(0) = 0, as there is no triangle with perimeter 0); the identity is A = num * den^(-1) in
  Q[[x]].
* The recurrence is stated over the integers, for every n > 11.
* Controls proved in the proof file: a(0..11) = 0, 0, 0, 1, 0, 2, 2, 6, 3, 7, 8, 14.
-/

namespace OMA.S_oeis_a308159

open Finset PowerSeries

/-- Integer-sided isosceles triangles with perimeter n, as side triples x <= y <= z. -/
def tri (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ (range (n + 1)) ×ˢ (range (n + 1))).filter (fun t =>
    1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n ∧ t.2.2 < t.1 + t.2.1 ∧
      (t.1 = t.2.1 ∨ t.2.1 = t.2.2))

/-- A308159(n): the sum of the largest sides. -/
def a (n : ℕ) : ℕ := ∑ t ∈ tri n, t.2.2

/-- The generating function. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's numerator and denominator. -/
noncomputable def num : ℚ⟦X⟧ := X ^ 3 * (1 + 2 * X ^ 2 + X ^ 3 + 4 * X ^ 4 + X ^ 5 + X ^ 6)

noncomputable def den : ℚ⟦X⟧ :=
  (1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2)

/-- Barker's conjectures: the generating function and the recurrence for n > 11. -/
theorem main : A = num * den⁻¹ ∧
    ∀ n : ℕ, 11 < n →
      (a n : ℤ) = a (n - 3) + 2 * a (n - 4) - 2 * a (n - 7) - a (n - 8) + a (n - 11) := by
  sorry

end OMA.S_oeis_a308159
