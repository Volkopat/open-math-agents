import Mathlib

/-!
# OEIS A308034: Barker's generating function and recurrence

Source: https://oeis.org/A308034 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Wesley Ivan Hurt, May 10 2019), offset 1: Number of partitions of n into 3 parts with at
least 1 part that is a nondivisor of n. Formula section: Conjectures from Colin Barker, May 11 2019:
G.f.: x^5*(2 - 3*x + 6*x^2 - 6*x^3 + 6*x^4 - 3*x^5) / ((1 - x)^3*(1 + x)*(1 - x + x^2)*(1 + x^2)*(1 +
x + x^2)). a(n) = 2*a(n-1) - 2*a(n-2) + 2*a(n-3) - a(n-4) + a(n-6) - 2*a(n-7) + 2*a(n-8) - 2*a(n-9) +
a(n-10) for n>10.

Formalization notes:
* A partition of n into 3 parts is a triple (x, y, z) of positive integers with x <= y <= z and
  x + y + z = n; a(n) counts those in which x, y or z does not divide n.
* The g.f. is the formal power series Sum a(n) x^n over the rationals; its constant coefficient is
  a(0) = 0 (there is no partition of 0 into 3 positive parts), so it is the g.f. of the sequence with
  offset 1. The claim is that it equals the numerator times the inverse of the denominator, whose
  constant term is 1. The recurrence is stated in the integers.
* `main` is the conjunction of Barker's two conjectures.
* Controls from the entry (proved in the proof file by kernel computation from the definition):
  a(1) = 0, a(5) = 2, a(6) = 1, a(7) = 4, a(10) = 8, a(11) = 10, a(12) = 9.
-/

namespace OMA.S_oeis_a308034

open Finset PowerSeries

/-- The partitions of n into 3 parts: triples (x, y, z) with 1 <= x <= y <= z and x + y + z = n. -/
def parts (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Icc 1 n ×ˢ Icc 1 n ×ˢ Icc 1 n).filter fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n

/-- A308034(n): the partitions of n into 3 parts with at least one part that does not divide n. -/
def a (n : ℕ) : ℕ := ((parts n).filter fun t => ¬ t.1 ∣ n ∨ ¬ t.2.1 ∣ n ∨ ¬ t.2.2 ∣ n).card

/-- The generating function Sum_{n >= 1} a(n) x^n (the coefficient a(0) is 0, there being no
partition of 0 into 3 parts). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's conjectures: the g.f. and the recurrence for n > 10. -/
theorem main :
    gf = X ^ 5 * (2 - 3 * X + 6 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 - 3 * X ^ 5) *
      ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2) * (1 + X ^ 2) * (1 + X + X ^ 2))⁻¹ ∧
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) + 2 * a (n - 3) -
      a (n - 4) + a (n - 6) - 2 * a (n - 7) + 2 * a (n - 8) - 2 * a (n - 9) + a (n - 10)) := by
  sorry

end OMA.S_oeis_a308034
