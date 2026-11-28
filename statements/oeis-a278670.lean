import Mathlib

/-!
# OEIS A278670: Barker's generating function and recurrence

Source: https://oeis.org/A278670 (OEIS Foundation, CC BY-SA 4.0).

Entry (R. H. Hardin, Nov 26 2016), offset 1: Number of n X 2 0..1 arrays with rows in
nondecreasing lexicographic order and columns in nonincreasing lexicographic order, but with exactly
one mistake. Data: 1, 8, 33, 99, 245, 532, 1050, 1926, ... The formula section states: Empirical: a(n) = (1/720)*n^6 + (1/48)*n^5 + (23/144)*n^4 + (19/48)*n^3 + (61/180)*n^2 + (1/12)*n.
Conjectures from Colin Barker, Feb 10 2019: (Start) G.f.: x*(1 + x - 2*x^2 + x^3) / (1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7. (End)

Formalization notes:
* An n X 2 array is a function `Fin n → Fin 2 × Fin 2` giving each row (x(i,0), x(i,1)), the rows
  read from the top.
* Rows are compared lexicographically, x(i,0) first: this is the order of `code r = 2 x(i,0) +
  x(i,1)`. The columns x(0,0), ..., x(n-1,0) and x(0,1), ..., x(n-1,1) are compared
  lexicographically from the top.
* A mistake is a violation of one of the required orders between neighbours: a pair of adjacent
  rows with row i + 1 lexicographically smaller than row i (n - 1 pairs), and, for the one pair of
  adjacent columns, the first column lexicographically smaller than the second. The array counts
  when the total number of mistakes is exactly 1.
* `ok` scans the rows from the top. It remembers the previous row (p0, p1), the number `k` of row
  mistakes so far, saturating at 2 (which stands for 2 or more), and the comparison `e` of the two
  columns read so far (0 equal so far, 1 the first column is larger, 2 the first column is
  smaller). `valid` starts the scan at the first row.
* This reading reproduces the entry's data a(1..34), checked in the proof file.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^7 = N(x) in
  Q[[x]], which is equivalent because the denominator has constant term 1. The recurrence is stated
  in the integers for every n > 7.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a278670

open PowerSeries

/-- A row (x(i,0), x(i,1)) read as a binary number, x(i,0) most significant: comparing codes compares
rows lexicographically. -/
def code (r : Fin 2 × Fin 2) : ℕ := 2 * r.1.val + r.2.val

/-- The mistake count `k` increased by one if `b`, saturating at 2. -/
def inc (k : Fin 3) (b : Bool) : Fin 3 := if b = true ∧ k.val < 2 then k + 1 else k

/-- The lexicographic comparison of the two columns read so far (0 equal so far, 1 the first column
is larger, 2 the first column is smaller), after the row (u, v). -/
def cmp (e : Fin 3) (u v : Fin 2) : Fin 3 :=
  if e = 0 then (if v.val < u.val then 1 else if u.val < v.val then 2 else 0) else e

/-- Scanning the rows below the row (p0, p1), with `k` row mistakes so far and the column comparison
`e`: at the end the total number of mistakes is exactly 1. -/
def ok : Fin 2 → Fin 2 → Fin 3 → Fin 3 → List (Fin 2 × Fin 2) → Bool
  | _, _, k, e, [] => decide (k.val + (if e = 2 then 1 else 0) = 1)
  | p0, p1, k, e, c :: l => ok c.1 c.2 (inc k (decide (code c < code (p0, p1)))) (cmp e c.1 c.2) l

/-- An n X 2 array, read as its list of rows from the top, has exactly one mistake. -/
def valid : List (Fin 2 × Fin 2) → Bool
  | [] => false
  | c :: l => ok c.1 c.2 0 (cmp 0 c.1 c.2) l

/-- A278670(n): the number of n X 2 binary arrays with exactly one mistake; row i is the pair
(x(i,0), x(i,1)). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 2 × Fin 2 => valid (List.ofFn x) = true).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * (1 - X) ^ 7 =
      X * (1 + X - 2 * X ^ 2 + X ^ 3) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 21 * (a (n - 2) : ℤ) + 35 * (a (n - 3) : ℤ) - 35 * (a (n - 4) : ℤ) + 21 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) + (a (n - 7) : ℤ) := by
  sorry

end OMA.S_oeis_a278670
