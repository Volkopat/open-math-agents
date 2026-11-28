import Mathlib

/-!
# OEIS A232950: Barker's generating function and closed form for n X 3 arrays over 0..3

Source: https://oeis.org/A232950 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A232950 (R. H. Hardin, Dec 02 2013), offset 1: Number of n X 3 0..3 arrays with no element
x(i,j) adjacent to value 3-x(i,j) horizontally, diagonally or antidiagonally, and top left
element zero.
Formula section:
Conjectures from Colin Barker, Oct 06 2018:
G.f.: 3*x*(3 - 2*x) / (1 - 15*x + 6*x^2).
a(n) = (2^(-1-n)*((15-sqrt(201))^n*(-3+sqrt(201)) + (3+sqrt(201))*(15+sqrt(201))^n)) /
sqrt(201).

Formalization notes:
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2)) in Fin 4 x Fin 4 x Fin 4.
* An element x adjacent to the value 3 - x means two neighboring cells whose values sum to 3. The
  listed directions are horizontal (x(i,j), x(i,j+1)), inside a row (hrow), and diagonal
  (x(i,j), x(i+1,j+1)) and antidiagonal (x(i,j), x(i+1,j-1)), between consecutive rows (ok); the
  vertical pair (x(i,j), x(i+1,j)) is not restricted. The top left element is x(0,0).
* The statement is the conjunction of both conjectures: the g.f. as the identity
  A(x) (1 - 15x + 6x^2) = 3x(3 - 2x) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (the offset is 1, so the constant term is 0), and the closed form
  in the reals for every n >= 1, with 2^(-1-n) an integer power.
* Controls proved in the proof file: the definition gives 9, 129, 1881, 27441, 400329, 5840289,
  85202361, 1242993681, 18133691049 for n = 1..9, the entry's data.
-/

namespace OMA.S_oeis_a232950

open PowerSeries Finset

/-- A row (x(i,0), x(i,1), x(i,2)) has no horizontal pair of cells with values summing to 3. -/
def hrow (r : Fin 4 × Fin 4 × Fin 4) : Prop :=
  r.1.val + r.2.1.val ≠ 3 ∧ r.2.1.val + r.2.2.val ≠ 3

/-- The row `s` may follow the row `r`: no diagonal pair (x(i,j), x(i+1,j+1)) and no
antidiagonal pair (x(i,j), x(i+1,j-1)) has values summing to 3. -/
def ok (r s : Fin 4 × Fin 4 × Fin 4) : Prop :=
  r.1.val + s.2.1.val ≠ 3 ∧ r.2.1.val + s.2.2.val ≠ 3 ∧ r.2.1.val + s.1.val ≠ 3 ∧
    r.2.2.val + s.2.1.val ≠ 3

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A232950: the number of n X 3 arrays with entries 0..3, given by their rows f i =
(x(i,0), x(i,1), x(i,2)), with no element adjacent to 3 minus itself horizontally, diagonally or
antidiagonally, and with top left element x(0,0) = 0. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 4 × Fin 4 × Fin 4)).filter
    (fun f => (∀ i, hrow (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)) ∧
      ∀ i : Fin n, i.val = 0 → (f i).1 = 0)).card

/-- Barker's conjectures: the g.f. 3x(3 - 2x)/(1 - 15x + 6x^2) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 15 * X + 6 * X ^ 2) =
      3 * X * (3 - 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (-1 - (n : ℤ)) * ((15 - Real.sqrt 201) ^ n * (-3 + Real.sqrt 201) +
        (3 + Real.sqrt 201) * (15 + Real.sqrt 201) ^ n)) / Real.sqrt 201 := by
  sorry

end OMA.S_oeis_a232950
