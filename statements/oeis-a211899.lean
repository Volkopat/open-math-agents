import Mathlib

/-!
# OEIS A211899: Barker's g.f. and recurrence for triangular n X n X n arrays colored in row major order with no element equal to any neighbor, containing n(n+1)/2-2

Source: https://oeis.org/A211899 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A211899 (R. H. Hardin, Apr 25 2012), offset 1: Number of triangular n X n X n arrays colored
with integers 0 upwards introduced in row major order, with no element equal to any neighbor, and
containing the value n(n+1)/2-2. Column 1 of A211904.
Formula section:
Conjectures from Colin Barker, Jul 20 2018:
G.f.: x^2*(1 + 2*x + 3*x^2 - 4*x^3 + x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>6.

Formalization notes:
* The cells of the triangular n X n X n array are the positions (i, j) with j ≤ i < n (`Cell n`),
  row i holding the positions 0..i. A coloring is a function x from the cells to the natural numbers
  (the integers 0 upwards).
* New values introduced in row major order (`RowMajorNew`): reading the rows from the top, each
  row from the left, every value smaller than an entry occurs at an earlier cell; equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each coloring
  stands for one partition of the cells into color classes.
* Neighbors (`Nbr`) in the triangular n X n X n array: row i holds the positions 0..i and is drawn
  centered under row i - 1 (as in the entry's examples), so position j of row i touches positions j
  - 1 and j + 1 of row i, positions j - 1 and j of row i - 1 and positions j and j + 1 of row i + 1
  (the triangular lattice). `Cond` asks that no element be equal to such an element.
* Containing the value n(n+1)/2-2: some entry equals n(n+1)/2 - 2, computed in the integers, so
  for n = 1 the value is -1 and a(1) = 0 as in the data.
* a(n) is the number of these colorings, `Set.ncard` of the set of functions (the set is finite:
  no value exceeds the number of cells).
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x) (1 -
  x)^5 = x^2(1 + 2x + 3x^2 - 4x^3 + x^4) in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the recurrence for every n
  > 6 in the integers.
* Controls proved in the proof file: the definition gives 0, 1, 7, 28, 76, 166, 316, 547, 883,
  1351 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a211899

open PowerSeries Finset

/-- The cells of the array: the positions (i, j) with j ≤ i < n, row i holding the positions 0..i. -/
def Cell (n : ℕ) := {p : Fin n × Fin n // p.2 ≤ p.1}

/-- The values of x are introduced in row major order (the rows from the top, each row from the
left): every value below x c occurs at an earlier cell. In particular the first entry is 0. -/
def RowMajorNew {n : ℕ} (x : Cell n → ℕ) : Prop :=
  ∀ c : Cell n, ∀ u < x c, ∃ c' : Cell n,
    (c'.1.1 < c.1.1 ∨ (c'.1.1 = c.1.1 ∧ c'.1.2 < c.1.2)) ∧ x c' = u

/-- c' is a neighbor of c in the triangular array, whose row i (positions 0..i) is drawn centered
under row i - 1: the next or previous position in the same row, positions j and j + 1 of the next
row, or positions j - 1 and j of the previous row, where j is the position of c. -/
def Nbr {n : ℕ} (c c' : Cell n) : Prop :=
  (c'.1.1.val = c.1.1.val ∧ (c'.1.2.val = c.1.2.val + 1 ∨ c.1.2.val = c'.1.2.val + 1)) ∨
    (c'.1.1.val = c.1.1.val + 1 ∧ (c'.1.2.val = c.1.2.val ∨ c'.1.2.val = c.1.2.val + 1)) ∨
    (c.1.1.val = c'.1.1.val + 1 ∧ (c.1.2.val = c'.1.2.val ∨ c.1.2.val = c'.1.2.val + 1))

/-- No element is equal to any neighbor. -/
def Cond {n : ℕ} (x : Cell n → ℕ) : Prop :=
  ∀ c c' : Cell n, Nbr c c' → x c ≠ x c'

/-- A211899(n): the number of colorings x of the triangular n X n X n array with the integers 0
upwards whose values are introduced in row major order, in which no element is equal to any neighbor
(`Cond`), and which contain the value n(n+1)/2 - 2 (computed in the integers). -/
noncomputable def a (n : ℕ) : ℕ :=
  {x : Cell n → ℕ | RowMajorNew x ∧ Cond x ∧ ∃ c, (x c : ℤ) = (n : ℤ) * (n + 1) / 2 - 2}.ncard

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X ^ 2 * (1 + 2 * X + 3 * X ^ 2 - 4 * X ^ 3 + X ^ 4) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) =
      5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a211899
