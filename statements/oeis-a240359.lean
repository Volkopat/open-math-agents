import Mathlib

/-!
# OEIS A240359: Barker's g.f. and recurrence for n X 2 arrays avoiding running and diagonal sums mod 4

Source: https://oeis.org/A240359 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A240359 (R. H. Hardin, Apr 04 2014), offset 1: Number of n X 2 0..3 arrays with no element equal to one plus the sum of elements to its left or two plus the sum of elements above it or two plus the sum of the elements diagonally to its northwest, modulo 4.
Formula section:
Empirical: a(n) = (1/40320)*n^8 - (1/2016)*n^7 + (7/576)*n^6 - (23/360)*n^5 + (1327/5760)*n^4 + (1271/288)*n^3 - (25027/672)*n^2 + (127387/840)*n - 223 for n>4.
Conjectures from Colin Barker, Oct 27 2018: (Start)
G.f.: x*(4 - 21*x + 52*x^2 - 72*x^3 + 54*x^4 - 8*x^5 - 32*x^6 + 55*x^7 - 67*x^8 + 66*x^9 - 46*x^10 + 20*x^11 - 4*x^12) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>13.
(End)

Formalization notes:
* An array is a function f : Fin n -> Fin 2 -> Fin 4, f i j the entry in row i and column j. The
  elements to the left of (i, j) are f i j' with j' < j, those above it are f i' j with i' < i, and
  those diagonally to its northwest are f i' j' with i' < i, j' < j and i - i' = j - j'. At every
  entry the value must differ from (1 + the sum of the elements to its left) mod 4, from
  (2 + the sum of the elements above it) mod 4 and from (2 + the sum of the elements
  diagonally to its northwest) mod 4, the sums taken over the natural numbers 0..3; empty
  sums are 0.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^9 = x(4 - 21x + 52x^2 - 72x^3 + 54x^4 - 8x^5 - 32x^6 + 55x^7 - 67x^8 + 66x^9 - 46x^10 + 20x^11 - 4x^12) in the formal power series ring over
  the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and
  the recurrence for every n > 13 as an identity of integers.
* Controls proved in the proof file: the definition gives 4, 15, 43, 111, 261, 571, 1171, 2278, 4235, 7570, 13076, 21918, 35774
  for n = 1..13, the entry's data.
-/

namespace OMA.S_oeis_a240359

open PowerSeries Finset

/-- No element equal to one plus the sum of the elements to its left, two plus the sum of the
elements above it, or two plus the sum of the elements diagonally to its northwest, modulo 4
(f i j: row i, column j; the northwest diagonal of (i, j) holds the f i' j' with i' < i, j' < j and
i - i' = j - j'). -/
def good {n : ℕ} (f : Fin n → Fin 2 → Fin 4) : Prop :=
  ∀ i j, (f i j).val ≠ (1 + ∑ j' ∈ Finset.Iio j, (f i j').val) % 4 ∧
    (f i j).val ≠ (2 + ∑ i' ∈ Finset.Iio i, (f i' j).val) % 4 ∧
    (f i j).val ≠ (2 + ∑ i' ∈ Finset.Iio i, ∑ j' ∈ Finset.Iio j,
      if i.val - i'.val = j.val - j'.val then (f i' j').val else 0) % 4

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A240359: the number of n X 2 0..3 arrays with no element equal to one plus the sum of elements to its left or two plus the sum of elements above it or two plus the sum of the elements diagonally to its northwest, modulo 4. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 2 → Fin 4)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 9 = X * (4 - 21 * X + 52 * X ^ 2 - 72 * X ^ 3 + 54 * X ^ 4 - 8 * X ^ 5 - 32 * X ^ 6 + 55 * X ^ 7 - 67 * X ^ 8 + 66 * X ^ 9 - 46 * X ^ 10 + 20 * X ^ 11 - 4 * X ^ 12) ∧
    ∀ n : ℕ, 13 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a240359
