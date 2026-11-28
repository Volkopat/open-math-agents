import Mathlib

/-!
# OEIS A240395: Barker's g.f. and recurrence for 3 X n arrays avoiding running and diagonal sums mod 4

Source: https://oeis.org/A240395 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A240395 (R. H. Hardin, Apr 04 2014), offset 1: Number of 3 X n 0..3 arrays with no element equal to zero plus the sum of elements to its left or one plus the sum of the elements above it or two plus the sum of the elements diagonally to its northwest, modulo 4.
Formula section:
Empirical: a(n) = (1/6)*n^4 - (5/6)*n^3 + (13/3)*n^2 + (31/3)*n - 48 for n>5.
Conjectures from Colin Barker, Oct 27 2018: (Start)
G.f.: x*(2 + 2*x - 8*x^2 + 2*x^3 + 18*x^4 - 26*x^5 + 29*x^6 - 29*x^7 + 20*x^8 - 6*x^9) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>10.
(End)

Formalization notes:
* An array is a function f : Fin 3 -> Fin n -> Fin 4, f i j the entry in row i and column j. The
  elements to the left of (i, j) are f i j' with j' < j, those above it are f i' j with i' < i, and
  those diagonally to its northwest are f i' j' with i' < i, j' < j and i - i' = j - j'. At every
  entry the value must differ from (0 + the sum of the elements to its left) mod 4, from
  (1 + the sum of the elements above it) mod 4 and from (2 + the sum of the elements
  diagonally to its northwest) mod 4, the sums taken over the natural numbers 0..3; empty
  sums are 0.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^5 = x(2 + 2x - 8x^2 + 2x^3 + 18x^4 - 26x^5 + 29x^6 - 29x^7 + 20x^8 - 6x^9) in the formal power series ring over
  the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and
  the recurrence for every n > 10 as an identity of integers.
* Controls proved in the proof file: the definition gives 2, 12, 32, 62, 118, 206, 351, 568, 882, 1322
  for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a240395

open PowerSeries Finset

/-- No element equal to the sum of the elements to its left, one plus the sum of the
elements above it, or two plus the sum of the elements diagonally to its northwest, modulo 4
(f i j: row i, column j; the northwest diagonal of (i, j) holds the f i' j' with i' < i, j' < j and
i - i' = j - j'). -/
def good {n : ℕ} (f : Fin 3 → Fin n → Fin 4) : Prop :=
  ∀ i j, (f i j).val ≠ (∑ j' ∈ Finset.Iio j, (f i j').val) % 4 ∧
    (f i j).val ≠ (1 + ∑ i' ∈ Finset.Iio i, (f i' j).val) % 4 ∧
    (f i j).val ≠ (2 + ∑ i' ∈ Finset.Iio i, ∑ j' ∈ Finset.Iio j,
      if i.val - i'.val = j.val - j'.val then (f i' j').val else 0) % 4

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A240395: the number of 3 X n 0..3 arrays with no element equal to zero plus the sum of elements to its left or one plus the sum of the elements above it or two plus the sum of the elements diagonally to its northwest, modulo 4. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 3 → Fin n → Fin 4)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 5 = X * (2 + 2 * X - 8 * X ^ 2 + 2 * X ^ 3 + 18 * X ^ 4 - 26 * X ^ 5 + 29 * X ^ 6 - 29 * X ^ 7 + 20 * X ^ 8 - 6 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a240395
