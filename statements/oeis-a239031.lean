import Mathlib

/-!
# OEIS A239031: Barker's g.f. and recurrence for 4 X n arrays avoiding running sums mod 3

Source: https://oeis.org/A239031 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A239031 (R. H. Hardin, Mar 09 2014), offset 1: Number of 4 X n 0..2 arrays with no element equal to the sum of elements to its left or one plus the sum of the elements above it, modulo 3.
Formula section:
Empirical: a(n) = (1/12)*n^4 - (1/6)*n^3 + (47/12)*n^2 - (29/6)*n + 5.
Conjectures from Colin Barker, Oct 25 2018: (Start)
G.f.: x*(4 - 9*x + 13*x^2 - 11*x^3 + 5*x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.
(End)

Formalization notes:
* An array is a function f : Fin 4 -> Fin n -> Fin 3, f i j the entry in row i and column j. The
  elements to the left of (i, j) are f i j' with j' < j, those above it are f i' j with i' < i. At
  every entry the value must differ from (0 + the sum of the elements to its left) mod 3 and
  from (1 + the sum of the elements above it) mod 3, the sums taken over the natural numbers
  0..2; empty sums are 0.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^5 = x(4 - 9x + 13x^2 - 11x^3 + 5x^4) in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the
  recurrence for every n > 5 as an identity of integers.
* Controls proved in the proof file: the definition gives 4, 11, 28, 59, 110
  for n = 1..5, the entry's data.
-/

namespace OMA.S_oeis_a239031

open PowerSeries Finset

/-- No element equal to the sum of the elements to its left or
one plus the sum of the elements above it, modulo 3 (f i j: row i, column j). -/
def good {n : ℕ} (f : Fin 4 → Fin n → Fin 3) : Prop :=
  ∀ i j, (f i j).val ≠ (∑ j' ∈ Finset.Iio j, (f i j').val) % 3 ∧
    (f i j).val ≠ (1 + ∑ i' ∈ Finset.Iio i, (f i' j).val) % 3

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A239031: the number of 4 X n 0..2 arrays with no element equal to the sum of elements to its left or one plus the sum of the elements above it, modulo 3. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 4 → Fin n → Fin 3)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 5 = X * (4 - 9 * X + 13 * X ^ 2 - 11 * X ^ 3 + 5 * X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a239031
