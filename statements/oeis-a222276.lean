import Mathlib

/-!
# OEIS A222276: Barker's g.f. and closed form for n X 3 arrays with no entry increasing mod 6 by 5

Source: https://oeis.org/A222276 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A222276 (R. H. Hardin, Feb 14 2013), offset 1: Number of n X 3 0..5 arrays with no entry
increasing mod 6 by 5 rightwards or downwards, starting with upper left zero. Column 3 of A222281.
Formula section:
Conjectures from Colin Barker, Mar 14 2018:
G.f.: 5*x*(5 - 19*x) / (1 - 92*x + 335*x^2).
a(n) = ((46-sqrt(1781))^n*(-801+19*sqrt(1781)) + (46+sqrt(1781))^n*(801+19*sqrt(1781))) / (134*sqrt(1781)).

Formalization notes:
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2)), each a triple in Fin 6 x Fin 6 x
  Fin 6 (column 0 first).
* An entry y increases mod 6 by 5 from its neighbor x when y = x + 5 mod 6. Rightwards means from
  x(i,j) to x(i,j+1) and downwards from x(i,j) to x(i+1,j); both are excluded everywhere. Starting
  with upper left zero means x(0,0) = 0.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x) (1 -
  92x + 335x^2) = 5x(5 - 19x) in the formal power series ring over the rationals, with A(x) = Sum_{n
  >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the reals for every n
  >= 1.
* Controls proved in the proof file: the definition gives 25, 2205, 194485, 17153945, 1513010465,
  133450391205, 11770577485085, 1038187247574145, 91570083319317865, 8076654937439905005 for n =
  1..10, the entry's data.
-/

namespace OMA.S_oeis_a222276

open PowerSeries Finset

/-- No entry of the row (x(i,0), x(i,1), x(i,2)) increases mod 6 by 5 rightwards:
x(i,j+1) is not x(i,j) + 5 mod 6. -/
def hrow (r : Fin 6 × Fin 6 × Fin 6) : Prop :=
  r.2.1.val ≠ (r.1.val + 5) % 6 ∧ r.2.2.val ≠ (r.2.1.val + 5) % 6

/-- The row `s` may lie directly below the row `r`: no entry increases mod 6 by 5 downwards,
x(i+1,j) is not x(i,j) + 5 mod 6. -/
def ok (r s : Fin 6 × Fin 6 × Fin 6) : Prop :=
  s.1.val ≠ (r.1.val + 5) % 6 ∧ s.2.1.val ≠ (r.2.1.val + 5) % 6 ∧
    s.2.2.val ≠ (r.2.2.val + 5) % 6

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A222276: the number of n X 3 arrays with entries 0..5, given by their rows
f i = (x(i,0), x(i,1), x(i,2)), with no entry increasing mod 6 by 5 rightwards or downwards
and with upper left entry x(0,0) = 0. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 6 × Fin 6 × Fin 6)).filter
    (fun f => (∀ i, hrow (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)) ∧
      ∀ i : Fin n, i.val = 0 → (f i).1 = 0)).card

/-- Barker's conjectures: the g.f. 5x(5 - 19x)/(1 - 92x + 335x^2) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 92 * X + 335 * X ^ 2) =
      5 * X * (5 - 19 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      ((46 - Real.sqrt 1781) ^ n * (-801 + 19 * Real.sqrt 1781) +
      (46 + Real.sqrt 1781) ^ n * (801 + 19 * Real.sqrt 1781)) / (134 * Real.sqrt 1781) := by
  sorry

end OMA.S_oeis_a222276
