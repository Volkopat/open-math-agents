import Mathlib

/-!
# OEIS A232951: Barker's g.f. and closed form for n X 4 0..3 arrays with no element next to 3 minus itself

Source: https://oeis.org/A232951 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A232951 (R. H. Hardin, Dec 02 2013), offset 1: Number of n X 4 0..3 arrays with no element
x(i,j) adjacent to value 3-x(i,j) horizontally, diagonally or antidiagonally, and top left element
zero. Column 4 of A232955.
Formula section:
Conjectures from Colin Barker, Oct 06 2018:
G.f.: 3*x*(9 - 22*x + 5*x^2) / ((1 - x)*(1 - 30*x + 5*x^2)).
a(n) = (55 + (15-2*sqrt(55))^n*(55+sqrt(55)) - (-55+sqrt(55))*(15+2*sqrt(55))^n)/55.

Formalization notes:
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2), x(i,3)), each a 4-tuple of
  entries 0..3. An element x is adjacent to the value 3 - x when a neighbor in one of the listed
  directions holds 3 - x, so two neighbors x, y are allowed together exactly when x + y is not 3
  (`adj`). The directions are horizontal (x(i,j), x(i,j+1)), diagonal (x(i,j), x(i+1,j+1)) and
  antidiagonal (x(i,j+1), x(i+1,j)); vertical neighbors are not constrained. Top left element zero
  means x(0,0) = 0.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - x)(1 - 30x + 5x^2) = 3x(9 - 22x + 5x^2) in the formal power series ring over the
  rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the
  closed form in the reals for every n >= 1.
* Controls proved in the proof file: the definition gives 27, 771, 22971, 685251, 20442651, 609853251, 18193384251, 542752261251, 16191600916251, 483034266181251, 14410069980856251, 429886928094781251 for
  n = 1..12, the entry's data.
-/

namespace OMA.S_oeis_a232951

open PowerSeries Finset

/-- Two entries x, y of 0..3 may be neighbors when y is not 3 - x, that is x + y is not 3. -/
def adj (x y : Fin 4) : Prop := x.val + y.val ≠ 3

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- The horizontal pairs (x(i,j), x(i,j+1)) of the row hold allowed neighbors. -/
def hrow (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) : Prop :=
  adj r.1 r.2.1 ∧ adj r.2.1 r.2.2.1 ∧ adj r.2.2.1 r.2.2.2

/-- The row `s` may lie directly below the row `r`: the diagonal pairs (x(i,j), x(i+1,j+1)) and the
antidiagonal pairs (x(i,j+1), x(i+1,j)) hold allowed neighbors. -/
def ok (r s : Fin 4 × Fin 4 × Fin 4 × Fin 4) : Prop :=
  adj r.1 s.2.1 ∧ adj r.2.1 s.2.2.1 ∧ adj r.2.2.1 s.2.2.2 ∧ adj r.2.1 s.1 ∧ adj r.2.2.1 s.2.1 ∧
    adj r.2.2.2 s.2.2.1

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A232951: the number of n X 4 arrays with entries 0..3, given by their rows, with no element
adjacent to 3 minus itself horizontally, diagonally or antidiagonally, and with x(0,0) = 0. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 4 × Fin 4 × Fin 4 × Fin 4)).filter
    (fun f => (∀ i, hrow (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)) ∧
      ∀ i : Fin n, i.val = 0 → (f i).1 = 0)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 30 * X + 5 * X ^ 2)) = 3 * X * (9 - 22 * X + 5 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (55 + (15 - 2 * Real.sqrt 55) ^ n * (55 + Real.sqrt 55) -
        (-55 + Real.sqrt 55) * (15 + 2 * Real.sqrt 55) ^ n) / 55 := by
  sorry

end OMA.S_oeis_a232951
