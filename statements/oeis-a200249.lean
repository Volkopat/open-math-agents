import Mathlib

/-!
# OEIS A200249: Barker's g.f. and closed form for 0..5 arrays above their running sums mod 6

Source: https://oeis.org/A200249 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A200249 (R. H. Hardin, Nov 15 2011), offset 1: Number of 0..5 arrays x(0..n-1) of n elements
with each no smaller than the sum of its previous elements modulo 6.
Formula section:
Empirical: a(n) = 3*a(n-1) +2*a(n-2).
Conjectures from Colin Barker, May 20 2018: (Start)
G.f.: 3*x*(2 + x) / (1 - 3*x - 2*x^2).
a(n) = (3*2^(-2-n)*((3-sqrt(17))^n*(-5+sqrt(17)) + (3+sqrt(17))^n*(5+sqrt(17)))) / sqrt(17).
(End)

Formalization notes:
* An array is a function x : Fin n -> Fin 6; the condition at every index i is
  (x 0 + ... + x (i - 1)) mod 6 <= x i, the sum taken over the natural numbers 0..5 (the empty sum
  is 0, so x 0 is free).
* The statement is the conjunction of the two parts of the site's problem: the g.f. as the identity
  A(x) (1 - 3x - 2x^2) = 3x(2 + x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form for every
  n >= 1 as an identity of real numbers, with 2^(-2-n) the integer power of the real number 2 and
  sqrt(17) the real square root.
* Controls proved in the proof file: the definition gives 6, 21, 75, 267, 951, 3387, 12063 for
  n = 1..7, the entry's data.
-/

namespace OMA.S_oeis_a200249

open PowerSeries Finset

/-- Each element no smaller than the sum of its previous elements modulo 6. -/
def good {n : ℕ} (x : Fin n → Fin 6) : Prop :=
  ∀ i, (∑ j ∈ Finset.Iio i, (x j).val) % 6 ≤ (x i).val

instance : ∀ {n : ℕ}, DecidablePred (@good n) := fun x => by unfold good; infer_instance

/-- A200249: the number of 0..5 arrays x(0..n-1) of n elements with each no smaller than the sum of
its previous elements modulo 6. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin n → Fin 6)).filter good).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 3 * X - 2 * X ^ 2) =
      3 * X * (2 + X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 3 * (2 : ℝ) ^ (-2 - (n : ℤ)) *
      ((3 - √17) ^ n * (-5 + √17) + (3 + √17) ^ n * (5 + √17)) / √17 := by
  sorry

end OMA.S_oeis_a200249
