import Mathlib

/-!
# OEIS A223197: Barker's g.f. and closed form for rolling cube footprints, n X 3

Source: https://oeis.org/A223197 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A223197 (R. H. Hardin, Mar 18 2013), offset 1: Rolling cube footprints: number of n X 3 0..5
arrays starting with 0 where 0..5 label faces of a cube and every array movement to a horizontal or
vertical neighbor moves across a corresponding cube edge. Column 3 of A223202.
Formula section:
Conjectures from Colin Barker, Mar 16 2018:
G.f.: 16*x*(1 - 4*x) / (1 - 40*x + 128*x^2).
a(n) = ((20-4*sqrt(17))^n*(-3+sqrt(17)) + (3+sqrt(17))*(4*(5+sqrt(17)))^n) / (4*sqrt(17)).

Formalization notes:
* The labels 0..5 are the faces of the cube, faces 2i and 2i + 1 being the two opposite faces
  perpendicular to the i-th coordinate axis; two faces share an edge exactly when they are
  perpendicular to different axes, so a movement across a cube edge joins two labels x, y with x / 2
  different from y / 2. Another numbering of the faces is an isomorphism of this face graph, and the
  rotation group of the cube is transitive on faces, so the count of arrays starting with 0 does not
  depend on the numbering.
* An array is given by its n rows f i = (x(i,0), x(i,1), x(i,2)). The neighbor pairs that must move
  across a corresponding cube edge are the horizontal pairs (x(i,j), x(i,j+1)) and the vertical
  pairs (x(i,j), x(i+1,j)). Starting with 0 means x(0,0) = 0.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x)
  (1 - 40x + 128x^2) = 16x(1 - 4x) in the formal power series ring over the rationals, with A(x) =
  Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the reals for
  every n >= 1.
* Controls proved in the proof file: the definition gives 16, 576, 20992, 765952, 27951104,
  1020002304, 37222350848, 1358333739008, 49568888651776, 1808888827478016 for n = 1..10, the
  entry's data; every face shares an edge with exactly 4 faces.
-/

namespace OMA.S_oeis_a223197

open PowerSeries Finset

/-- The faces 0..5 of the cube, numbered so that faces 2i and 2i + 1 are the two opposite faces
perpendicular to the i-th coordinate axis. Two faces share an edge exactly when they are
perpendicular to different axes. -/
def adj (x y : Fin 6) : Prop := x.val / 2 ≠ y.val / 2

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- The horizontal movements inside the row (x(i,0), x(i,1), x(i,2)) are between adjacent
labels. -/
def hrow (r : Fin 6 × Fin 6 × Fin 6) : Prop := adj r.1 r.2.1 ∧ adj r.2.1 r.2.2

/-- The row `s` may lie directly below the row `r`: the vertical pairs (x(i,j), x(i+1,j)) hold
adjacent labels. -/
def ok (r s : Fin 6 × Fin 6 × Fin 6) : Prop :=
  adj r.1 s.1 ∧ adj r.2.1 s.2.1 ∧ adj r.2.2 s.2.2

instance : DecidablePred hrow := fun r => by unfold hrow; infer_instance

instance : DecidableRel ok := fun r s => by unfold ok; infer_instance

/-- A223197: the number of n X 3 arrays of labels 0..5, given by their rows
f i = (x(i,0), x(i,1), x(i,2)), starting with x(0,0) = 0, in which every movement to a
horizontal or vertical neighbor moves across a corresponding cube edge. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 6 × Fin 6 × Fin 6)).filter
    (fun f => (∀ i, hrow (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)) ∧
      ∀ i : Fin n, i.val = 0 → (f i).1 = 0)).card

/-- Barker's conjectures: the g.f. 16x(1 - 4x)/(1 - 40x + 128x^2) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 40 * X + 128 * X ^ 2) =
      16 * X * (1 - 4 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      ((20 - 4 * Real.sqrt 17) ^ n * (-3 + Real.sqrt 17) +
        (3 + Real.sqrt 17) * (4 * (5 + Real.sqrt 17)) ^ n) / (4 * Real.sqrt 17) := by
  sorry

end OMA.S_oeis_a223197
