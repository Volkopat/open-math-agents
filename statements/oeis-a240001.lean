import Mathlib

/-!
# OEIS A240001: Barker's g.f. and recurrence for 2 X n arrays avoiding running and diagonal sums mod 4

Source: https://oeis.org/A240001 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A240001 (R. H. Hardin, Mar 30 2014), offset 1: Number of 2 X n 0..3 arrays with no element equal to one plus the sum of elements to its left or two plus the sum of the elements above it or one plus the sum of the elements diagonally to its northwest, modulo 4.
Formula section:
Empirical: a(n) = (1/6)*n^3 + 1*n^2 + (23/6)*n.
Conjectures from Colin Barker, Oct 27 2018: (Start)
G.f.: x*(5 - 7*x + 3*x^2) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.
(End)

Formalization notes:
* An array is a function f : Fin 2 -> Fin n -> Fin 4, f i j the entry in row i and column j. The
  elements to the left of (i, j) are f i j' with j' < j, those above it are f i' j with i' < i, and
  those diagonally to its northwest are f i' j' with i' < i, j' < j and i - i' = j - j'. At every
  entry the value must differ from (1 + the sum of the elements to its left) mod 4, from
  (2 + the sum of the elements above it) mod 4 and from (1 + the sum of the elements
  diagonally to its northwest) mod 4, the sums taken over the natural numbers 0..3; empty
  sums are 0.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^4 = x(5 - 7x + 3x^2) in the formal power series ring over
  the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and
  the recurrence for every n > 4 as an identity of integers.
* Controls proved in the proof file: the definition gives 5, 13, 25, 42
  for n = 1..4, the entry's data.
-/

namespace OMA.S_oeis_a240001

open PowerSeries Finset

/-- No element equal to one plus the sum of the elements to its left, two plus the sum of the
elements above it, or one plus the sum of the elements diagonally to its northwest, modulo 4
(f i j: row i, column j; the northwest diagonal of (i, j) holds the f i' j' with i' < i, j' < j and
i - i' = j - j'). -/
def good {n : ℕ} (f : Fin 2 → Fin n → Fin 4) : Prop :=
  ∀ i j, (f i j).val ≠ (1 + ∑ j' ∈ Finset.Iio j, (f i j').val) % 4 ∧
    (f i j).val ≠ (2 + ∑ i' ∈ Finset.Iio i, (f i' j).val) % 4 ∧
    (f i j).val ≠ (1 + ∑ i' ∈ Finset.Iio i, ∑ j' ∈ Finset.Iio j,
      if i.val - i'.val = j.val - j'.val then (f i' j').val else 0) % 4

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A240001: the number of 2 X n 0..3 arrays with no element equal to one plus the sum of elements to its left or two plus the sum of the elements above it or one plus the sum of the elements diagonally to its northwest, modulo 4. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 2 → Fin n → Fin 4)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 4 = X * (5 - 7 * X + 3 * X ^ 2) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a240001
