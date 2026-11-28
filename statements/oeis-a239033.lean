import Mathlib

/-!
# OEIS A239033: Barker's g.f. and recurrence for 6 X n arrays avoiding running sums mod 3

Source: https://oeis.org/A239033 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A239033 (R. H. Hardin, Mar 09 2014), offset 1: Number of 6 X n 0..2 arrays with no element equal to the sum of elements to its left or one plus the sum of the elements above it, modulo 3.
Formula section:
Empirical: a(n) = (1/8640)*n^9 - (61/20160)*n^8 + (263/3360)*n^7 - (1439/1440)*n^6 + (29843/2880)*n^5 - (194227/2880)*n^4 + (668597/2160)*n^3 - (1477657/1680)*n^2 + (59263/42)*n - 943 for n>2.
Conjectures from Colin Barker, Oct 25 2018: (Start)
G.f.: x*(8 - 37*x + 142*x^2 - 339*x^3 + 592*x^4 - 811*x^5 + 996*x^6 - 1020*x^7 + 792*x^8 - 377*x^9 + 88*x^10 + 8*x^11) / (1 - x)^10.
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>12.
(End)

Formalization notes:
* An array is a function f : Fin 6 -> Fin n -> Fin 3, f i j the entry in row i and column j. The
  elements to the left of (i, j) are f i j' with j' < j, those above it are f i' j with i' < i. At
  every entry the value must differ from (0 + the sum of the elements to its left) mod 3 and
  from (1 + the sum of the elements above it) mod 3, the sums taken over the natural numbers
  0..2; empty sums are 0.
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - x)^10 = x(8 - 37x + 142x^2 - 339x^3 + 592x^4 - 811x^5 + 996x^6 - 1020x^7 + 792x^8 - 377x^9 + 88x^10 + 8x^11) in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the
  recurrence for every n > 12 as an identity of integers.
* Controls proved in the proof file: the definition gives 8, 43, 212, 806, 2592, 7265, 18362, 42809, 93464, 193157, 380900, 721154
  for n = 1..12, the entry's data.
-/

namespace OMA.S_oeis_a239033

open PowerSeries Finset

/-- No element equal to the sum of the elements to its left or
one plus the sum of the elements above it, modulo 3 (f i j: row i, column j). -/
def good {n : ℕ} (f : Fin 6 → Fin n → Fin 3) : Prop :=
  ∀ i j, (f i j).val ≠ (∑ j' ∈ Finset.Iio j, (f i j').val) % 3 ∧
    (f i j).val ≠ (1 + ∑ i' ∈ Finset.Iio i, (f i' j).val) % 3

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A239033: the number of 6 X n 0..2 arrays with no element equal to the sum of elements to its left or one plus the sum of the elements above it, modulo 3. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin n → Fin 3)).filter good).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 10 = X * (8 - 37 * X + 142 * X ^ 2 - 339 * X ^ 3 + 592 * X ^ 4 - 811 * X ^ 5 + 996 * X ^ 6 - 1020 * X ^ 7 + 792 * X ^ 8 - 377 * X ^ 9 + 88 * X ^ 10 + 8 * X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a239033
