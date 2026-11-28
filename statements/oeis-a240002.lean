import Mathlib

/-!
# OEIS A240002: Barker's g.f. and recurrence for 3 X n arrays avoiding running and diagonal sums mod 4

Source: https://oeis.org/A240002 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A240002 (R. H. Hardin, Mar 30 2014), offset 1: Number of 3 X n 0..3 arrays with no element equal to one plus the sum of elements to its left or two plus the sum of the elements above it or one plus the sum of the elements diagonally to its northwest, modulo 4.
Formula section:
Empirical: a(n) = (1/40320)*n^8 + (1/2016)*n^7 + (7/576)*n^6 + (17/360)*n^5 + (6367/5760)*n^4 - (935/288)*n^3 + (28145/672)*n^2 - (114913/840)*n + 237 for n>6.
Conjectures from Colin Barker, Oct 27 2018: (Start)
G.f.: x*(12 - 47*x + 73*x^2 + 4*x^3 - 244*x^4 + 558*x^5 - 737*x^6 + 651*x^7 - 375*x^8 + 86*x^9 + 91*x^10 - 128*x^11 + 80*x^12 - 27*x^13 + 4*x^14) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>15.
(End)

Formalization notes:
* An array is a function f : Fin 3 -> Fin n -> Fin 4, f i j the entry in row i and column j. The
  elements to the left of (i, j) are f i j' with j' < j, those above it are f i' j with i' < i, and
  those diagonally to its northwest are f i' j' with i' < i, j' < j and i - i' = j - j'. At every
  entry the value must differ from (1 + the sum of the elements to its left) mod 4, from
  (2 + the sum of the elements above it) mod 4 and from (1 + the sum of the elements
  diagonally to its northwest) mod 4, the sums taken over the natural numbers 0..3; empty
  sums are 0.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^9 = x(12 - 47x + 73x^2 + 4x^3 - 244x^4 + 558x^5 - 737x^6 + 651x^7 - 375x^8 + 86x^9 + 91x^10 - 128x^11 + 80x^12 - 27x^13 + 4x^14) in the formal power series ring over
  the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and
  the recurrence for every n > 15 as an identity of integers.
* Controls proved in the proof file: the definition gives 12, 61, 190, 526, 1262, 2766, 5647, 10878, 19971, 35180, 59780, 98414, 157524, 245879, 375214
  for n = 1..15, the entry's data.
-/

namespace OMA.S_oeis_a240002

open PowerSeries Finset

/-- No element equal to one plus the sum of the elements to its left, two plus the sum of the
elements above it, or one plus the sum of the elements diagonally to its northwest, modulo 4
(f i j: row i, column j; the northwest diagonal of (i, j) holds the f i' j' with i' < i, j' < j and
i - i' = j - j'). -/
def good {n : ℕ} (f : Fin 3 → Fin n → Fin 4) : Prop :=
  ∀ i j, (f i j).val ≠ (1 + ∑ j' ∈ Finset.Iio j, (f i j').val) % 4 ∧
    (f i j).val ≠ (2 + ∑ i' ∈ Finset.Iio i, (f i' j).val) % 4 ∧
    (f i j).val ≠ (1 + ∑ i' ∈ Finset.Iio i, ∑ j' ∈ Finset.Iio j,
      if i.val - i'.val = j.val - j'.val then (f i' j').val else 0) % 4

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A240002: the number of 3 X n 0..3 arrays with no element equal to one plus the sum of elements to its left or two plus the sum of the elements above it or one plus the sum of the elements diagonally to its northwest, modulo 4. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 3 → Fin n → Fin 4)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 9 = X * (12 - 47 * X + 73 * X ^ 2 + 4 * X ^ 3 - 244 * X ^ 4 + 558 * X ^ 5 - 737 * X ^ 6 + 651 * X ^ 7 - 375 * X ^ 8 + 86 * X ^ 9 + 91 * X ^ 10 - 128 * X ^ 11 + 80 * X ^ 12 - 27 * X ^ 13 + 4 * X ^ 14) ∧
    ∀ n : ℕ, 15 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a240002
