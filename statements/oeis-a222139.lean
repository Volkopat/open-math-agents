import Mathlib

/-!
# OEIS A222139: Barker's g.f. and closed form for n X 3 arrays with no entry increasing mod 5 by 4

Source: https://oeis.org/A222139 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A222139 (R. H. Hardin, Feb 09 2013), offset 1: Number of n X 3 0..4 arrays with no entry
increasing mod 5 by 4 rightwards or downwards, starting with upper left zero. Column 3 of A222144.
Formula section:
Conjectures from Colin Barker, Mar 14 2018:
G.f.: 4*x*(4 - 11*x) / (1 - 45*x + 116*x^2).
a(n) = (2^(-1-n)*((45-sqrt(1561))^n*(-433+11*sqrt(1561)) + (45+sqrt(1561))^n*(433+11*sqrt(1561)))) / (29*sqrt(1561)).

Formalization notes:
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2)), each a triple in Fin 5 x Fin 5 x
  Fin 5 (column 0 first).
* An entry y increases mod 5 by 4 from its neighbor x when y = x + 4 mod 5. Rightwards means from
  x(i,j) to x(i,j+1) and downwards from x(i,j) to x(i+1,j); both are excluded everywhere. Starting
  with upper left zero means x(0,0) = 0.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x) (1 -
  45x + 116x^2) = 4x(4 - 11x) in the formal power series ring over the rationals, with A(x) = Sum_{n
  >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the reals for every n
  >= 1, with 2^(-1-n) as an integer power.
* Controls proved in the proof file: the definition gives 16, 676, 28564, 1206964, 50999956,
  2154990196, 91058563924, 3847656513844, 162581749707796, 6869850581244916 for n = 1..10, the
  entry's data.
-/

namespace OMA.S_oeis_a222139

open PowerSeries Finset

/-- No entry of the row (x(i,0), x(i,1), x(i,2)) increases mod 5 by 4 rightwards:
x(i,j+1) is not x(i,j) + 4 mod 5. -/
def hrow (r : Fin 5 × Fin 5 × Fin 5) : Prop :=
  r.2.1.val ≠ (r.1.val + 4) % 5 ∧ r.2.2.val ≠ (r.2.1.val + 4) % 5

/-- The row `s` may lie directly below the row `r`: no entry increases mod 5 by 4 downwards,
x(i+1,j) is not x(i,j) + 4 mod 5. -/
def ok (r s : Fin 5 × Fin 5 × Fin 5) : Prop :=
  s.1.val ≠ (r.1.val + 4) % 5 ∧ s.2.1.val ≠ (r.2.1.val + 4) % 5 ∧
    s.2.2.val ≠ (r.2.2.val + 4) % 5

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A222139: the number of n X 3 arrays with entries 0..4, given by their rows
f i = (x(i,0), x(i,1), x(i,2)), with no entry increasing mod 5 by 4 rightwards or downwards
and with upper left entry x(0,0) = 0. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 5 × Fin 5 × Fin 5)).filter
    (fun f => (∀ i, hrow (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)) ∧
      ∀ i : Fin n, i.val = 0 → (f i).1 = 0)).card

/-- Barker's conjectures: the g.f. 4x(4 - 11x)/(1 - 45x + 116x^2) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 45 * X + 116 * X ^ 2) =
      4 * X * (4 - 11 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (-1 - (n : ℤ)) * ((45 - Real.sqrt 1561) ^ n * (-433 + 11 * Real.sqrt 1561) +
      (45 + Real.sqrt 1561) ^ n * (433 + 11 * Real.sqrt 1561))) / (29 * Real.sqrt 1561) := by
  sorry

end OMA.S_oeis_a222139
