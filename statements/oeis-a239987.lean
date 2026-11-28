import Mathlib

/-!
# OEIS A239987: Barker's g.f. and recurrence for 3 X n arrays avoiding running and diagonal sums mod 4

Source: https://oeis.org/A239987 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A239987 (R. H. Hardin, Mar 30 2014), offset 1: Number of 3 X n 0..3 arrays with no element equal to zero plus the sum of elements to its left or two plus the sum of the elements above it or one plus the sum of the elements diagonally to its northwest, modulo 4.
Formula section:
Empirical: a(n) = (1/24)*n^4 - (1/4)*n^3 + (71/24)*n^2 - (43/4)*n + 23 for n>3.
Conjectures from Colin Barker, Oct 27 2018: (Start)
G.f.: x*(3 - 9*x + 13*x^2 - 13*x^3 + 13*x^4 - 8*x^5 + x^6 + x^7) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>8.
(End)

Formalization notes:
* An array is a function f : Fin 3 -> Fin n -> Fin 4, f i j the entry in row i and column j. The
  elements to the left of (i, j) are f i j' with j' < j, those above it are f i' j with i' < i, and
  those diagonally to its northwest are f i' j' with i' < i, j' < j and i - i' = j - j'. At every
  entry the value must differ from (0 + the sum of the elements to its left) mod 4, from
  (2 + the sum of the elements above it) mod 4 and from (1 + the sum of the elements
  diagonally to its northwest) mod 4, the sums taken over the natural numbers 0..3; empty
  sums are 0.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^5 = x(3 - 9x + 13x^2 - 13x^3 + 13x^4 - 8x^5 + x^6 + x^7) in the formal power series ring over
  the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and
  the recurrence for every n > 8 as an identity of integers.
* Controls proved in the proof file: the definition gives 3, 6, 13, 22, 38, 65, 107, 169
  for n = 1..8, the entry's data.
-/

namespace OMA.S_oeis_a239987

open PowerSeries Finset

/-- No element equal to the sum of the elements to its left, two plus the sum of the
elements above it, or one plus the sum of the elements diagonally to its northwest, modulo 4
(f i j: row i, column j; the northwest diagonal of (i, j) holds the f i' j' with i' < i, j' < j and
i - i' = j - j'). -/
def good {n : ℕ} (f : Fin 3 → Fin n → Fin 4) : Prop :=
  ∀ i j, (f i j).val ≠ (∑ j' ∈ Finset.Iio j, (f i j').val) % 4 ∧
    (f i j).val ≠ (2 + ∑ i' ∈ Finset.Iio i, (f i' j).val) % 4 ∧
    (f i j).val ≠ (1 + ∑ i' ∈ Finset.Iio i, ∑ j' ∈ Finset.Iio j,
      if i.val - i'.val = j.val - j'.val then (f i' j').val else 0) % 4

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A239987: the number of 3 X n 0..3 arrays with no element equal to zero plus the sum of elements to its left or two plus the sum of the elements above it or one plus the sum of the elements diagonally to its northwest, modulo 4. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 3 → Fin n → Fin 4)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 5 = X * (3 - 9 * X + 13 * X ^ 2 - 13 * X ^ 3 + 13 * X ^ 4 - 8 * X ^ 5 + X ^ 6 + X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a239987
