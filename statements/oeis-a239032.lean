import Mathlib

/-!
# OEIS A239032: Barker's g.f. and recurrence for 5 X n arrays avoiding running sums mod 3

Source: https://oeis.org/A239032 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A239032 (R. H. Hardin, Mar 09 2014), offset 1: Number of 5 X n 0..2 arrays with no element equal to the sum of elements to its left or one plus the sum of the elements above it, modulo 3.
Formula section:
Empirical: a(n) = (1/144)*n^6 - (17/240)*n^5 + (169/144)*n^4 - (81/16)*n^3 + (1463/72)*n^2 - (1001/30)*n + 25 for n>1.
Conjectures from Colin Barker, Oct 25 2018: (Start)
G.f.: x*(4 - 12*x + 26*x^2 - 33*x^3 + 25*x^4 - 6*x^5 - 3*x^6 + 4*x^7) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>8.
(End)

Formalization notes:
* An array is a function f : Fin 5 -> Fin n -> Fin 3, f i j the entry in row i and column j. The
  elements to the left of (i, j) are f i j' with j' < j, those above it are f i' j with i' < i. At
  every entry the value must differ from (0 + the sum of the elements to its left) mod 3 and
  from (1 + the sum of the elements above it) mod 3, the sums taken over the natural numbers
  0..2; empty sums are 0.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^7 = x(4 - 12x + 26x^2 - 33x^3 + 25x^4 - 6x^5 - 3x^6 + 4x^7) in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the
  recurrence for every n > 8 as an identity of integers.
* Controls proved in the proof file: the definition gives 4, 16, 54, 149, 354, 757, 1495, 2773
  for n = 1..8, the entry's data.
-/

namespace OMA.S_oeis_a239032

open PowerSeries Finset

/-- No element equal to the sum of the elements to its left or
one plus the sum of the elements above it, modulo 3 (f i j: row i, column j). -/
def good {n : ℕ} (f : Fin 5 → Fin n → Fin 3) : Prop :=
  ∀ i j, (f i j).val ≠ (∑ j' ∈ Finset.Iio j, (f i j').val) % 3 ∧
    (f i j).val ≠ (1 + ∑ i' ∈ Finset.Iio i, (f i' j).val) % 3

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A239032: the number of 5 X n 0..2 arrays with no element equal to the sum of elements to its left or one plus the sum of the elements above it, modulo 3. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 5 → Fin n → Fin 3)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 7 = X * (4 - 12 * X + 26 * X ^ 2 - 33 * X ^ 3 + 25 * X ^ 4 - 6 * X ^ 5 - 3 * X ^ 6 + 4 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a239032
