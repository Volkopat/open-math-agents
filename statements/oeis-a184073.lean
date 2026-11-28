import Mathlib

/-!
# A184073: sorted 0..2 arrays with smooth 2 X 2 subblock sums

Source: https://oeis.org/A184073
Credit: @adanthar

A184073(n) (offset 1) is the number of (n+1) X 2 0..2 arrays with rows and columns in nondecreasing
order and with no 2 X 2 subblock sum differing from a horizontal or vertical neighbor subblock
sum by more than one. Data: 29, 58, 150, 335, 728, 1499, 2968, 5645, 10331, 18242, ...

Conjectures from Colin Barker, Apr 12 2018:
* G.f.: x*(29 - 203*x + 672*x^2 - 1363*x^3 + 1895*x^4 - 1939*x^5 + 1573*x^6 - 1117*x^7 + 749*x^8 - 450*x^9 + 209*x^10 - 65*x^11 + 12*x^12 - x^13) / (1 - x)^9.
* a(n) = (1290240 - 1768560*n + 1559788*n^2 - 343756*n^3 + 72569*n^4 - 4480*n^5 + 602*n^6 - 4*n^7 + n^8) / 40320 for n>5.
* a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>14.

Reading of the source, as in statements/oeis-a184063.lean (the (n+1) X 2 binary case):
* Rows are compared with each other, and columns with each other, lexicographically, with the
  first entry (leftmost, resp. topmost) most significant and the usual order of `0, 1, 2`; this is the order of
  rows and columns read as base-3 numbers, and it agrees with the examples in the entry.
  The rows must be nondecreasing from top to bottom, the columns from left to right.
* A 2 X 2 subblock consists of two adjacent rows and two adjacent columns. Two subblocks are
  horizontal (resp. vertical) neighbors when one is shifted by one column (resp. one row)
  from the other; their sums may differ by at most one.
* The generating function is that of the sequence from offset 1: the coefficient of `X ^ 0` is
  set to `0`, and the identity is multiplied out by `(1 - X) ^ 9` in `ℤ⟦X⟧`.
-/

namespace OMA.S_oeis_a184073

/-- Row `i` of `A`, read from left to right. -/
def row {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 3) (i : Fin (n + 1)) : List (Fin 3) :=
  List.ofFn (A i)

/-- Column `j` of `A`, read from top to bottom. -/
def col {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 3) (j : Fin 2) : List (Fin 3) :=
  List.ofFn (fun i => A i j)

/-- The rows are in lexicographically nondecreasing order from top to bottom. -/
def RowsNondecreasing {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 3) : Prop :=
  ∀ i : Fin n, row A i.castSucc ≤ row A i.succ

/-- The columns are in lexicographically nondecreasing order from left to right. -/
def ColsNondecreasing {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 3) : Prop :=
  ∀ j : Fin 1, col A j.castSucc ≤ col A j.succ

/-- The sum of the 2 X 2 subblock in rows `i`, `i + 1` and columns `j`, `j + 1`. -/
def subblockSum {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 3) (i : Fin n) (j : Fin 1) : ℕ :=
  (A i.castSucc j.castSucc).val + (A i.castSucc j.succ).val +
    (A i.succ j.castSucc).val + (A i.succ j.succ).val

/-- The subblocks `p` and `q` (given by their top-left corners) are horizontal or vertical
neighbors, `q` lying one column to the right of, or one row below, `p`. -/
def Neighbors {n : ℕ} (p q : Fin n × Fin 1) : Prop :=
  (p.1 = q.1 ∧ p.2.val + 1 = q.2.val) ∨ (p.1.val + 1 = q.1.val ∧ p.2 = q.2)

/-- No subblock sum differs from a horizontal or vertical neighbor subblock sum by more
than one. -/
def SmoothSubblocks {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 3) : Prop :=
  ∀ p q : Fin n × Fin 1, Neighbors p q →
    subblockSum A p.1 p.2 ≤ subblockSum A q.1 q.2 + 1 ∧
      subblockSum A q.1 q.2 ≤ subblockSum A p.1 p.2 + 1

/-- The arrays counted by A184073. -/
def IsValid {n : ℕ} (A : Fin (n + 1) → Fin 2 → Fin 3) : Prop :=
  RowsNondecreasing A ∧ ColsNondecreasing A ∧ SmoothSubblocks A

/-- `a n` is the number of valid (n+1) X 2 0..2 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin (n + 1) → Fin 2 → Fin 3 // IsValid A}

open PowerSeries in
/-- Colin Barker's conjectures for A184073: the generating function, the closed form and the
recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 9 =
      X * (29 - 203 * X + 672 * X ^ 2 - 1363 * X ^ 3 + 1895 * X ^ 4 - 1939 * X ^ 5 +
        1573 * X ^ 6 - 1117 * X ^ 7 + 749 * X ^ 8 - 450 * X ^ 9 + 209 * X ^ 10 - 65 * X ^ 11 +
        12 * X ^ 12 - X ^ 13) ∧
    (∀ n : ℕ, 5 < n → 40320 * (a n : ℤ) = 1290240 - 1768560 * n + 1559788 * n ^ 2 -
      343756 * n ^ 3 + 72569 * n ^ 4 - 4480 * n ^ 5 + 602 * n ^ 6 - 4 * n ^ 7 + n ^ 8) ∧
    (∀ n : ℕ, 14 < n →
      (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) +
        126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a184073
