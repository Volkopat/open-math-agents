import Mathlib

/-!
# OEIS A239024: Barker's g.f. and closed form for n X 2 arrays avoiding running sums mod 3

Source: https://oeis.org/A239024 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A239024 (R. H. Hardin, Mar 09 2014), offset 1: Number of n X 2 0..2 arrays with no element
equal to the sum of elements to its left or one plus the sum of elements above it, modulo 3.
Formula section:
Conjectures from Colin Barker, Oct 25 2018: (Start)
G.f.: x*(1 + 3*x - x^2 - 4*x^3) / ((1 - x)*(1 + x)*(1 - 2*x)*(1 + 2*x)).
a(n) = (2 + (-2)^n + 2*(-1)^n + 7*2^n) / 12.
(End)

Formalization notes:
* An array is a function f : Fin n -> Fin 2 -> Fin 3, f i j the entry in row i and column j. The
  elements to the left of (i, j) are f i j' with j' < j, the elements above it are f i' j with
  i' < i; the condition at every entry is that its value differs from (sum of the elements to its
  left) mod 3 and from (1 + sum of the elements above it) mod 3, the sums taken over the natural
  numbers 0, 1, 2. Empty sums are 0.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - x)(1 + x)(1 - 2x)(1 + 2x) = x(1 + 3x - x^2 - 4x^3) in the formal power series ring
  over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and
  the closed form for every n >= 1 as an identity of rationals.
* Controls proved in the proof file: the definition gives 1, 3, 4 for n = 1, 2, 3, and 11 for
  n = 4, the entry's data.
-/

namespace OMA.S_oeis_a239024

open PowerSeries Finset

/-- No element equal to the sum of the elements to its left or one plus the sum of the elements
above it, modulo 3 (f i j: row i, column j). -/
def good {n : ℕ} (f : Fin n → Fin 2 → Fin 3) : Prop :=
  ∀ i j, (f i j).val ≠ (∑ j' ∈ Finset.Iio j, (f i j').val) % 3 ∧
    (f i j).val ≠ (1 + ∑ i' ∈ Finset.Iio i, (f i' j).val) % 3

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun f => by unfold good; infer_instance

/-- A239024: the number of n X 2 0..2 arrays with no element equal to the sum of elements to its
left or one plus the sum of elements above it, modulo 3. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 2 → Fin 3)).filter good).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) = X * (1 + 3 * X - X ^ 2 - 4 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2 + (-2) ^ n + 2 * (-1) ^ n + 7 * 2 ^ n) / 12 := by
  sorry

end OMA.S_oeis_a239024
