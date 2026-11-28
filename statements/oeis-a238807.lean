import Mathlib

/-!
# OEIS A238807: Barker's g.f. and recurrence for n X 3 arrays avoiding running sums mod 3

Source: https://oeis.org/A238807 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A238807 (R. H. Hardin, Mar 05 2014), offset 1: Number of n X 3 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of the sum of elements above it, modulo 3.
Formula section:
Empirical: a(n) = (1/360)*n^6 - (1/30)*n^5 + (7/9)*n^4 - (65/12)*n^3 + (11959/360)*n^2 - (1631/20)*n + 83 for n>2.
Conjectures from Colin Barker, Oct 24 2018: (Start)
G.f.: x*(4 - 13*x + 27*x^2 - 43*x^3 + 51*x^4 - 41*x^5 + 27*x^6 - 16*x^7 + 6*x^8) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>9.
(End)

Formalization notes:
* An array is a function f : Fin n -> Fin 3 -> Fin 3, f i j the entry in row i and column j. The
  elements to the left of (i, j) are f i j' with j' < j, those above it are f i' j with i' < i. At
  every entry the value must differ from (1 + the sum of the elements to its left) mod 3 and
  from (1 + the sum of the elements above it) mod 3, the sums taken over the natural numbers
  0..2; empty sums are 0.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^7 = x(4 - 13x + 27x^2 - 43x^3 + 51x^4 - 41x^5 + 27x^6 - 16x^7 + 6x^8) in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the
  recurrence for every n > 9 as an identity of integers.
* Controls proved in the proof file: the definition gives 4, 15, 48, 118, 254, 498, 916, 1605, 2702
  for n = 1..9, the entry's data.
-/

namespace OMA.S_oeis_a238807

open PowerSeries Finset

/-- No element equal to one plus the sum of the elements to its left or
one plus the sum of the elements above it, modulo 3 (f i j: row i, column j). -/
def good {n : ℕ} (f : Fin n → Fin 3 → Fin 3) : Prop :=
  ∀ i j, (f i j).val ≠ (1 + ∑ j' ∈ Finset.Iio j, (f i j').val) % 3 ∧
    (f i j).val ≠ (1 + ∑ i' ∈ Finset.Iio i, (f i' j).val) % 3

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A238807: the number of n X 3 0..2 arrays with no element equal to one plus the sum of elements to its left or one plus the sum of the sum of elements above it, modulo 3. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 3 → Fin 3)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 7 = X * (4 - 13 * X + 27 * X ^ 2 - 43 * X ^ 3 + 51 * X ^ 4 - 41 * X ^ 5 + 27 * X ^ 6 - 16 * X ^ 7 + 6 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a238807
