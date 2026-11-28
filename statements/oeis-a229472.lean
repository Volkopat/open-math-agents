import Mathlib

/-!
# OEIS A229472: Barker's g.f. and closed form for defective 4-colorings of an n X 1 array with exactly one mistake

Source: https://oeis.org/A229472 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @ppleskov.

Entry A229472 (R. H. Hardin, Sep 24 2013), offset 1: Number of defective 4-colorings of an n X 1
0..3 array connected horizontally, antidiagonally and vertically with exactly one mistake, and
colors introduced in row-major 0..3 order. Column 1 of A229479.
Formula section:
Conjectures from Colin Barker, Mar 16 2018:
G.f.: x^2*(1 - 6*x + 12*x^2 - 8*x^3 + 3*x^4) / ((1 - x)^2*(1 - 3*x)^2).
a(n) = (27+3^n) * (n-1) / 54 for n>2.

Formalization notes:
* An array is a function x : Fin n -> Fin 1 -> Fin 4, x i j being the color (0..3) of the cell in
  row i and column j (rows numbered from the top).
* The cells are connected horizontally (cell (i,j) with (i,j+1)), vertically ((i,j) with (i+1,j))
  and antidiagonally ((i,j) with (i+1,j-1)); each connection is counted once. A mistake is a
  connection whose two cells have the same color, and `mistakes x` counts them (for an n X 1 array
  only the vertical connections occur). The array is counted when it has exactly one mistake.
* Colors introduced in row-major 0..3 order (`RowMajorNew`): reading the array row by row, each row
  from left to right, every color smaller than an entry occurs before that entry (not every color
  has to occur).
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) ((1 - x)^2 (1 - 3x)^2) = x^2 (1 - 6x + 12x^2 - 8x^3 + 3x^4) in the formal power series ring
  over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and
  the closed form over the rationals for every n > 2.
* A direct enumeration of this definition gives 0, 1, 2, 6, 20, 70 for n = 1..6, the entry's data.
-/

namespace OMA.S_oeis_a229472

open PowerSeries Finset

/-- The colors of the array x are introduced in row major order: every color below x(i,j) already
occurs at an earlier position in row major order, in a row i' < i or in row i at a column j' < j. -/
def RowMajorNew {R C K : ℕ} (x : Fin R → Fin C → Fin K) : Prop :=
  ∀ i j, ∀ u : Fin K, u < x i j → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = u

instance {R C K : ℕ} : DecidablePred (@RowMajorNew R C K) := fun x => by
  unfold RowMajorNew; infer_instance

/-- The number of mistakes of x: the connections, horizontal ((i,j) to (i,j+1)), vertical ((i,j)
to (i+1,j)) or antidiagonal ((i,j) to (i+1,j-1)), between two cells of the same color; each
connection is counted once, from its cell (i,j). -/
def mistakes {R C K : ℕ} (x : Fin R → Fin C → Fin K) : ℕ :=
  ((univ : Finset ((Fin R × Fin C) × (Fin R × Fin C))).filter (fun pq =>
    ((pq.2.1 = pq.1.1 ∧ pq.2.2.val = pq.1.2.val + 1) ∨
      (pq.2.1.val = pq.1.1.val + 1 ∧ pq.2.2 = pq.1.2) ∨
      (pq.2.1.val = pq.1.1.val + 1 ∧ pq.2.2.val + 1 = pq.1.2.val)) ∧
    x pq.1.1 pq.1.2 = x pq.2.1 pq.2.2)).card

/-- A229472(n): the number of 4-colorings of an n X 1 array with exactly one mistake and the colors
introduced in row major order. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 1 → Fin 4)).filter (fun x => mistakes x = 1 ∧ RowMajorNew x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 2 * (1 - 3 * X) ^ 2) =
      X ^ 2 * (1 - 6 * X + 12 * X ^ 2 - 8 * X ^ 3 + 3 * X ^ 4) ∧
    ∀ n : ℕ, 2 < n → (a n : ℚ) = (27 + 3 ^ n) * (n - 1) / 54 := by
  sorry

end OMA.S_oeis_a229472
