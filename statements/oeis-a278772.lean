import Mathlib

/-!
# OEIS A278772: Barker's generating function and recurrence

Source: https://oeis.org/A278772 (OEIS Foundation, CC BY-SA 4.0).

Entry (R. H. Hardin, Nov 28 2016), offset 1: Number of n X 2 0..1 arrays with rows in
nondecreasing lexicographic order and columns in nonincreasing lexicographic order, but with exactly
two mistakes. Data: 0, 2, 20, 117, 503, 1750, 5209, 13751, ... The formula section states: Empirical: a(n) = (1/3628800)*n^10 + (1/80640)*n^9 + (1/3780)*n^8 + (17/8064)*n^7 + (1513/172800)*n^6 + (167/11520)*n^5 + (12329/362880)*n^4 + (197/4032)*n^3 - (2167/50400)*n^2 - (11/168)*n.
Conjectures from Colin Barker, Feb 10 2019: (Start) G.f.: x^2*(2 - 2*x + 7*x^2 - 14*x^3 + 12*x^4 - 5*x^5 + x^6) / (1 - x)^11. a(n) = 11*a(n-1) - 55*a(n-2) + 165*a(n-3) - 330*a(n-4) + 462*a(n-5) - 462*a(n-6) + 330*a(n-7) - 165*a(n-8) + 55*a(n-9) - 11*a(n-10) + a(n-11) for n>11. (End)

Formalization notes:
* An n X 2 array is a function `Fin n → Fin 2 × Fin 2` giving each row (x(i,0), x(i,1)), the rows
  read from the top.
* Rows are compared lexicographically, x(i,0) first: this is the order of `code r = 2 x(i,0) +
  x(i,1)`. The columns x(0,0), ..., x(n-1,0) and x(0,1), ..., x(n-1,1) are compared
  lexicographically from the top.
* A mistake is a violation of one of the required orders between neighbours: a pair of adjacent
  rows with row i + 1 lexicographically smaller than row i (n - 1 pairs), and, for the one pair of
  adjacent columns, the first column lexicographically smaller than the second. The array counts
  when the total number of mistakes is exactly 2.
* `ok` scans the rows from the top. It remembers the previous row (p0, p1), the number `k` of row
  mistakes so far, saturating at 3 (which stands for 3 or more), and the comparison `e` of the two
  columns read so far (0 equal so far, 1 the first column is larger, 2 the first column is
  smaller). `valid` starts the scan at the first row.
* This reading reproduces the entry's data a(1..29), checked in the proof file.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^11 = N(x) in
  Q[[x]], which is equivalent because the denominator has constant term 1. The recurrence is stated
  in the integers for every n > 11.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a278772

open PowerSeries

/-- A row (x(i,0), x(i,1)) read as a binary number, x(i,0) most significant: comparing codes compares
rows lexicographically. -/
def code (r : Fin 2 × Fin 2) : ℕ := 2 * r.1.val + r.2.val

/-- The mistake count `k` increased by one if `b`, saturating at 3. -/
def inc (k : Fin 4) (b : Bool) : Fin 4 := if b = true ∧ k.val < 3 then k + 1 else k

/-- The lexicographic comparison of the two columns read so far (0 equal so far, 1 the first column
is larger, 2 the first column is smaller), after the row (u, v). -/
def cmp (e : Fin 3) (u v : Fin 2) : Fin 3 :=
  if e = 0 then (if v.val < u.val then 1 else if u.val < v.val then 2 else 0) else e

/-- Scanning the rows below the row (p0, p1), with `k` row mistakes so far and the column comparison
`e`: at the end the total number of mistakes is exactly 2. -/
def ok : Fin 2 → Fin 2 → Fin 4 → Fin 3 → List (Fin 2 × Fin 2) → Bool
  | _, _, k, e, [] => decide (k.val + (if e = 2 then 1 else 0) = 2)
  | p0, p1, k, e, c :: l => ok c.1 c.2 (inc k (decide (code c < code (p0, p1)))) (cmp e c.1 c.2) l

/-- An n X 2 array, read as its list of rows from the top, has exactly two mistakes. -/
def valid : List (Fin 2 × Fin 2) → Bool
  | [] => false
  | c :: l => ok c.1 c.2 0 (cmp 0 c.1 c.2) l

/-- A278772(n): the number of n X 2 binary arrays with exactly two mistakes; row i is the pair
(x(i,0), x(i,1)). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 2 × Fin 2 => valid (List.ofFn x) = true).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * (1 - X) ^ 11 =
      X ^ 2 * (2 - 2 * X + 7 * X ^ 2 - 14 * X ^ 3 + 12 * X ^ 4 - 5 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = 11 * (a (n - 1) : ℤ) - 55 * (a (n - 2) : ℤ) + 165 * (a (n - 3) : ℤ) - 330 * (a (n - 4) : ℤ) + 462 * (a (n - 5) : ℤ) - 462 * (a (n - 6) : ℤ) + 330 * (a (n - 7) : ℤ) - 165 * (a (n - 8) : ℤ) + 55 * (a (n - 9) : ℤ) - 11 * (a (n - 10) : ℤ) + (a (n - 11) : ℤ) := by
  sorry

end OMA.S_oeis_a278772
