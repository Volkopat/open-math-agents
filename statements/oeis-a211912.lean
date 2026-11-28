import Mathlib

/-!
# OEIS A211912: Barker's g.f. and recurrence for lower triangular n X n arrays colored in row major order with no element equal to any horizontal, vertical, diagonal or antidiagonal neighbor, containing n(n+1)/2-3

Source: https://oeis.org/A211912 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A211912 (R. H. Hardin, Apr 25 2012), offset 1: Number of lower triangular n X n arrays colored
with integers 0 upwards introduced in row major order, with no element equal to any horizontal,
vertical, diagonal or antidiagonal neighbor, and containing the value n(n+1)/2-3. Column 2 of
A211916.
Formula section:
Conjectures from Colin Barker, Jul 20 2018:
G.f.: x^2*(1 + x + 160*x^2 + 296*x^3 - 93*x^4 - 104*x^5 + 66*x^6 - 13*x^7 + x^8) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>10.

Formalization notes:
* The cells of the lower triangular n X n array are the positions (i, j) with j ≤ i < n (`Cell
  n`), row i holding the positions 0..i. A coloring is a function x from the cells to the natural
  numbers (the integers 0 upwards).
* New values introduced in row major order (`RowMajorNew`): reading the rows from the top, each
  row from the left, every value smaller than an entry occurs at an earlier cell; equivalently the
  first entry is 0 and every entry is at most 1 + the largest entry before it, so that each coloring
  stands for one partition of the cells into color classes.
* Neighbors (`Nbr`): the horizontal, vertical, diagonal and antidiagonal neighbors, that is the
  other cells at row distance and column distance at most 1, |i - i'| and |j - j'| written with
  truncated subtraction. `Cond` asks that no element be equal to such an element.
* Containing the value n(n+1)/2-3: some entry equals n(n+1)/2 - 3, computed in the integers, so
  for n = 1 the value is -2 and a(1) = 0 as in the data.
* a(n) is the number of these colorings, `Set.ncard` of the set of functions (the set is finite:
  no value exceeds the number of cells).
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x) (1 -
  x)^9 = x^2(1 + x + 160x^2 + 296x^3 - 93x^4 - 104x^5 + 66x^6 - 13x^7 + x^8) in the formal power
  series ring over the rationals, with A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term
  is 0), and the recurrence for every n > 10 in the integers.
* Controls proved in the proof file: the definition gives 0, 1, 10, 214, 1946, 10431, 40561,
  127275, 342434, 820396 for n = 1..10, the entry's data.
-/

namespace OMA.S_oeis_a211912

open PowerSeries Finset

/-- The cells of the array: the positions (i, j) with j ≤ i < n, row i holding the positions 0..i. -/
def Cell (n : ℕ) := {p : Fin n × Fin n // p.2 ≤ p.1}

/-- The values of x are introduced in row major order (the rows from the top, each row from the
left): every value below x c occurs at an earlier cell. In particular the first entry is 0. -/
def RowMajorNew {n : ℕ} (x : Cell n → ℕ) : Prop :=
  ∀ c : Cell n, ∀ u < x c, ∃ c' : Cell n,
    (c'.1.1 < c.1.1 ∨ (c'.1.1 = c.1.1 ∧ c'.1.2 < c.1.2)) ∧ x c' = u

/-- c' is a horizontal, vertical, diagonal or antidiagonal neighbor of c: a cell other than c at row
distance and column distance at most 1 (distances written with truncated subtraction). -/
def Nbr {n : ℕ} (c c' : Cell n) : Prop :=
  (c.1.1.val - c'.1.1.val) + (c'.1.1.val - c.1.1.val) ≤ 1 ∧
    (c.1.2.val - c'.1.2.val) + (c'.1.2.val - c.1.2.val) ≤ 1 ∧
    0 < (c.1.1.val - c'.1.1.val) + (c'.1.1.val - c.1.1.val) +
      ((c.1.2.val - c'.1.2.val) + (c'.1.2.val - c.1.2.val))

/-- No element is equal to any horizontal, vertical, diagonal or antidiagonal neighbor. -/
def Cond {n : ℕ} (x : Cell n → ℕ) : Prop :=
  ∀ c c' : Cell n, Nbr c c' → x c ≠ x c'

/-- A211912(n): the number of colorings x of the lower triangular n X n array with the integers 0
upwards whose values are introduced in row major order, in which no element is equal to any
horizontal, vertical, diagonal or antidiagonal neighbor (`Cond`), and which contain the value
n(n+1)/2 - 3 (computed in the integers). -/
noncomputable def a (n : ℕ) : ℕ :=
  {x : Cell n → ℕ | RowMajorNew x ∧ Cond x ∧ ∃ c, (x c : ℤ) = (n : ℤ) * (n + 1) / 2 - 3}.ncard

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X ^ 2 * (1 + X + 160 * X ^ 2 + 296 * X ^ 3 - 93 * X ^ 4 - 104 * X ^ 5 + 66 * X ^ 6 -
        13 * X ^ 7 + X ^ 8) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) =
      9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) -
        84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a211912
