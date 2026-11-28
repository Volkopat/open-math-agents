import Mathlib

/-!
# OEIS A232921: Barker's generating function and closed form for 2 X n arrays over 0..2

Source: https://oeis.org/A232921 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A232921 (R. H. Hardin, Dec 02 2013), offset 1: Number of 2 X n 0..2 arrays with no element
x(i,j) adjacent to value 2-x(i,j) horizontally, diagonally or antidiagonally.
Formula section:
Conjectures from Colin Barker, Oct 06 2018:
G.f.: 9*x / (1 - 2*x - 2*x^2).
a(n) = (-3)*(sqrt(3)*((1-sqrt(3))^n - (1+sqrt(3))^n)) / 2.

Formalization notes:
* An array is given by its n columns f j = (x(0,j), x(1,j)) in Fin 3 x Fin 3 (row 0 first).
* An element x adjacent to the value 2 - x means two neighboring cells whose values sum to 2. The
  listed directions are horizontal (x(i,j), x(i,j+1)), diagonal (x(0,j), x(1,j+1)) and
  antidiagonal (x(0,j+1), x(1,j)); the vertical pair (x(0,j), x(1,j)) is not restricted. All
  these pairs join consecutive columns, so the condition is ok (f j) (f (j+1)) for every j.
* The statement is the conjunction of both conjectures: the g.f. as the identity
  A(x) (1 - 2x - 2x^2) = 9x in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (the offset is 1, so the constant term is 0), and the closed form
  in the reals for every n >= 1.
* Controls proved in the proof file: the definition gives 9, 18, 54, 144, 396, 1080, 2952, 8064,
  22032, 60192, 164448, 449280, 1227456 for n = 1..13, the entry's data.
-/

namespace OMA.S_oeis_a232921

open PowerSeries Finset

/-- Two consecutive columns `c` (column j) and `d` (column j + 1), each written as (row 0, row 1),
are compatible when no horizontal, diagonal or antidiagonal pair of cells between them has values
summing to 2. -/
def ok (c d : Fin 3 × Fin 3) : Prop :=
  c.1.val + d.1.val ≠ 2 ∧ c.2.val + d.2.val ≠ 2 ∧ c.1.val + d.2.val ≠ 2 ∧ d.1.val + c.2.val ≠ 2

instance : DecidableRel ok := fun c d => by unfold ok; infer_instance

/-- A232921: the number of 2 X n arrays with entries 0..2, given by their columns f j =
(x(0,j), x(1,j)), with no element adjacent to 2 minus itself horizontally, diagonally or
antidiagonally. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 3 × Fin 3)).filter
    (fun f => ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j))).card

/-- Barker's conjectures: the g.f. 9x/(1 - 2x - 2x^2) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 2 * X - 2 * X ^ 2) =
      9 * X ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (-3) * (Real.sqrt 3 * ((1 - Real.sqrt 3) ^ n - (1 + Real.sqrt 3) ^ n)) / 2 := by
  sorry

end OMA.S_oeis_a232921
