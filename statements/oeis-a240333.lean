import Mathlib

/-!
# OEIS A240333: Barker's g.f. and recurrence for n X 2 arrays avoiding running and diagonal sums mod 4

Source: https://oeis.org/A240333 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A240333 (R. H. Hardin, Apr 04 2014), offset 1: Number of n X 2 0..3 arrays with no element equal to two plus the sum of elements to its left or two plus the sum of elements above it or one plus the sum of the elements diagonally to its northwest, modulo 4.
Formula section:
Empirical: a(n) = (1/30)*n^5 + (1/24)*n^4 + (23/12)*n^3 - (193/24)*n^2 + (581/20)*n - 30 for n>2.
Conjectures from Colin Barker, Oct 27 2018: (Start)
G.f.: x*(4 - 9*x + 18*x^2 - 18*x^3 + 14*x^4 - 6*x^5 - x^6 + 2*x^7) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>8.
(End)

Formalization notes:
* An array is a function f : Fin n -> Fin 2 -> Fin 4, f i j the entry in row i and column j. The
  elements to the left of (i, j) are f i j' with j' < j, those above it are f i' j with i' < i, and
  those diagonally to its northwest are f i' j' with i' < i, j' < j and i - i' = j - j'. At every
  entry the value must differ from (2 + the sum of the elements to its left) mod 4, from
  (2 + the sum of the elements above it) mod 4 and from (1 + the sum of the elements
  diagonally to its northwest) mod 4, the sums taken over the natural numbers 0..3; empty
  sums are 0.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^6 = x(4 - 9x + 18x^2 - 18x^3 + 14x^4 - 6x^5 - x^6 + 2x^7) in the formal power series ring over
  the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and
  the recurrence for every n > 8 as an identity of integers.
* Controls proved in the proof file: the definition gives 4, 15, 48, 125, 284, 582, 1097, 1932
  for n = 1..8, the entry's data.
-/

namespace OMA.S_oeis_a240333

open PowerSeries Finset

/-- No element equal to two plus the sum of the elements to its left, two plus the sum of the
elements above it, or one plus the sum of the elements diagonally to its northwest, modulo 4
(f i j: row i, column j; the northwest diagonal of (i, j) holds the f i' j' with i' < i, j' < j and
i - i' = j - j'). -/
def good {n : ℕ} (f : Fin n → Fin 2 → Fin 4) : Prop :=
  ∀ i j, (f i j).val ≠ (2 + ∑ j' ∈ Finset.Iio j, (f i j').val) % 4 ∧
    (f i j).val ≠ (2 + ∑ i' ∈ Finset.Iio i, (f i' j).val) % 4 ∧
    (f i j).val ≠ (1 + ∑ i' ∈ Finset.Iio i, ∑ j' ∈ Finset.Iio j,
      if i.val - i'.val = j.val - j'.val then (f i' j').val else 0) % 4

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A240333: the number of n X 2 0..3 arrays with no element equal to two plus the sum of elements to its left or two plus the sum of elements above it or one plus the sum of the elements diagonally to its northwest, modulo 4. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 2 → Fin 4)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 6 = X * (4 - 9 * X + 18 * X ^ 2 - 18 * X ^ 3 + 14 * X ^ 4 - 6 * X ^ 5 - X ^ 6 + 2 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a240333
