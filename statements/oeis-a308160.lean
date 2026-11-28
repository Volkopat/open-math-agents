import Mathlib

/-!
# OEIS A308160: Barker's generating function and recurrence

Source: https://oeis.org/A308160 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Wesley Ivan Hurt, May 14 2019), offset 1: Take all the integer-sided isosceles triangles
with perimeter n and sides a, b, and c such that a <= b <= c. a(n) is the sum of all the b's.
Data: 0, 0, 1, 0, 2, 2, 5, 3, 7, 7, 12, 9, 15, ... Formula lines: Conjectures from Colin Barker,
May 15 2019: G.f.: x^3*(1 - x + 2*x^2 + x^4) / ((1 - x)^3*(1 + x)^2*(1 + x^2)^2).
a(n) = a(n-1) + 2*a(n-4) - 2*a(n-5) - a(n-8) + a(n-9) for n>9.

Formalization notes:
* An integer-sided triangle with perimeter n is a triple of positive integers a <= b <= c with
  a + b + c = n and c < a + b (nondegenerate); it is isosceles when a = b or b = c (equilateral
  triangles included once). This is Hurt's double-sum formula in the entry, and it reproduces the
  data. The statement follows the one for the sibling A308159 (largest sides), with b in place of
  c.
* The generating function is the formal power series sum_{n >= 0} a(n) x^n over the rationals
  (a(0) = 0, as there is no triangle with perimeter 0); the identity is A = num * den^(-1) in
  Q[[x]].
* The recurrence is stated over the integers, for every n > 9.
* Controls proved in the proof file: a(1..26) = 0, 0, 1, 0, 2, 2, 5, 3, 7, 7, 12, 9, 15, 15, 22,
  18, 26, 26, 35, 30, 40, 40, 51, 45, 57, 57, the entry's data.
-/

namespace OMA.S_oeis_a308160

open Finset PowerSeries

/-- Integer-sided isosceles triangles with perimeter n, as side triples a <= b <= c. -/
def tri (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ (range (n + 1)) ×ˢ (range (n + 1))).filter (fun t =>
    1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n ∧ t.2.2 < t.1 + t.2.1 ∧
      (t.1 = t.2.1 ∨ t.2.1 = t.2.2))

/-- A308160(n): the sum of the middle sides b. -/
def a (n : ℕ) : ℕ := ∑ t ∈ tri n, t.2.1

/-- The generating function. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's numerator and denominator. -/
noncomputable def num : ℚ⟦X⟧ := X ^ 3 * (1 - X + 2 * X ^ 2 + X ^ 4)

noncomputable def den : ℚ⟦X⟧ := (1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 2

/-- Barker's conjectures: the generating function and the recurrence for n > 9. -/
theorem main : A = num * den⁻¹ ∧
    ∀ n : ℕ, 9 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 4) - 2 * a (n - 5) - a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a308160
