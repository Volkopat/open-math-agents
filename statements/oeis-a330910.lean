import Mathlib

/-!
# OEIS A330910: Barker's generating function and recurrence

Source: https://oeis.org/A330910 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Enrique Navarrete, May 01 2020), offset 0: a(n-5) is the number of nonempty subsets of
{1,2,...,n} such that the difference of successive elements is at least 5. Example: for n=11,
a(6) = 22 and the sets are: {1,6}, {1,7}, ..., {6,11}, {1,6,11}. Formula section: Conjectures from
Colin Barker, May 17 2020: G.f.: x / ((1 - x)^2*(1 - x + x^2)*(1 - x^2 - x^3)). a(n) = 3*a(n-1) -
3*a(n-2) + a(n-3) + a(n-5) - 2*a(n-6) + a(n-7) for n>6.

Formalization notes:
* The counted subsets have at least two elements: the example lists only such sets for n = 11, and
  the data start a(0) = 0 for the subsets of {1,...,5} (with the five singletons a(0) would be 5).
  So a(n) counts the subsets of {1, ..., n+5} with at least two elements in which any two elements
  differ by at least 5, which for a set is the same as successive elements differing by at least 5.
* The g.f. is the formal power series Sum_{n >= 0} a(n) x^n over the rationals, and the claim is that
  it equals x times the inverse of the denominator, whose constant term is 1. The recurrence is
  stated in the integers.
* `main` is the conjunction of Barker's two conjectures.
* Controls from the entry (proved in the proof file): a(0..6) = 0, 1, 3, 6, 10, 15, 22, the first
  five by kernel computation over the subsets.
-/

namespace OMA.S_oeis_a330910

open Finset PowerSeries

/-- The subsets of {1, ..., n} with at least two elements whose successive elements differ by at
least 5 (equivalently, any two elements differ by at least 5). -/
def sets (n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter fun S => 2 ≤ S.card ∧ ∀ x ∈ S, ∀ y ∈ S, x < y → x + 5 ≤ y

/-- A330910(n) = the number of such subsets of {1, ..., n + 5}. -/
def a (n : ℕ) : ℕ := (sets (n + 5)).card

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's conjectures: the g.f. and the recurrence for n > 6. -/
theorem main :
    gf = X * ((1 - X) ^ 2 * (1 - X + X ^ 2) * (1 - X ^ 2 - X ^ 3))⁻¹ ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) +
      a (n - 5) - 2 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a330910
