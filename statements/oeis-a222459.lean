import Mathlib

/-!
# OEIS A222459: Barker's g.f. and closed form for n X 3 arrays with no entry increasing mod 8 by 7

Source: https://oeis.org/A222459 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A222459 (R. H. Hardin, Feb 21 2013), offset 1: Number of n X 3 0..7 arrays with no entry
increasing mod 8 by 7 rightwards or downwards, starting with upper left zero. Column 3 of A222462.
Formula section:
Conjectures from Colin Barker, Mar 15 2018:
G.f.: 7*x*(7 - 41*x) / (1 - 270*x + 1547*x^2).
a(n) = ((135-sqrt(16678))^n*(-5294+41*sqrt(16678)) + (135+sqrt(16678))^n*(5294+41*sqrt(16678))) / (442*sqrt(16678)).

Formalization notes:
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2)), each a triple in Fin 8 x Fin 8 x
  Fin 8 (column 0 first).
* An entry y increases mod 8 by 7 from its neighbor x when y = x + 7 mod 8. Rightwards means from
  x(i,j) to x(i,j+1) and downwards from x(i,j) to x(i+1,j); both are excluded everywhere. Starting
  with upper left zero means x(0,0) = 0.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x) (1 -
  270x + 1547x^2) = 7x(7 - 41x) in the formal power series ring over the rationals, with A(x) =
  Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the reals for
  every n >= 1.
* Controls proved in the proof file: the definition gives 49, 12943, 3418807, 903055069,
  238535974201, 63007686842527, 16643060295393343, 4396153388210813341, 1161214600539946100449,
  306727092854223318882703 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a222459

open PowerSeries Finset

/-- No entry of the row (x(i,0), x(i,1), x(i,2)) increases mod 8 by 7 rightwards:
x(i,j+1) is not x(i,j) + 7 mod 8. -/
def hrow (r : Fin 8 × Fin 8 × Fin 8) : Prop :=
  r.2.1.val ≠ (r.1.val + 7) % 8 ∧ r.2.2.val ≠ (r.2.1.val + 7) % 8

/-- The row `s` may lie directly below the row `r`: no entry increases mod 8 by 7 downwards,
x(i+1,j) is not x(i,j) + 7 mod 8. -/
def ok (r s : Fin 8 × Fin 8 × Fin 8) : Prop :=
  s.1.val ≠ (r.1.val + 7) % 8 ∧ s.2.1.val ≠ (r.2.1.val + 7) % 8 ∧
    s.2.2.val ≠ (r.2.2.val + 7) % 8

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A222459: the number of n X 3 arrays with entries 0..7, given by their rows
f i = (x(i,0), x(i,1), x(i,2)), with no entry increasing mod 8 by 7 rightwards or downwards
and with upper left entry x(0,0) = 0. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 8 × Fin 8 × Fin 8)).filter
    (fun f => (∀ i, hrow (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)) ∧
      ∀ i : Fin n, i.val = 0 → (f i).1 = 0)).card

/-- Barker's conjectures: the g.f. 7x(7 - 41x)/(1 - 270x + 1547x^2) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 270 * X + 1547 * X ^ 2) =
      7 * X * (7 - 41 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      ((135 - Real.sqrt 16678) ^ n * (-5294 + 41 * Real.sqrt 16678) +
      (135 + Real.sqrt 16678) ^ n * (5294 + 41 * Real.sqrt 16678)) / (442 * Real.sqrt 16678) := by
  sorry

end OMA.S_oeis_a222459
