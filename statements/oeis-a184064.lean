import Mathlib

/-!
# A184064: sorted binary arrays with smooth 2 X 2 subblock sums

Source: https://oeis.org/A184064
Credit: @adanthar

A184064(n) (offset 1) is the number of (n+1) X 3 binary arrays with rows and columns in nondecreasing
order and with no 2 X 2 subblock sum differing from a horizontal or vertical neighbor subblock
sum by more than one. Data: 11, 16, 36, 73, 134, 225, 354, 529, 758, 1049, ...

Conjectures from Colin Barker, Apr 11 2018:
* G.f.: x*(11 - 28*x + 38*x^2 - 19*x^3 + 5*x^4 - x^5 + 2*x^6) / (1 - x)^4.
* a(n) = (4*n^3 - 15*n^2 + 74*n - 93) / 3 for n>3.
* a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>7.

Reading of the source, as in statements/oeis-a184063.lean (the (n+1) X 2 binary case):
* Rows are compared with each other, and columns with each other, lexicographically, with the
  first entry (leftmost, resp. topmost) most significant and `false < true`; this is the order of
  rows and columns read as binary numbers, and it agrees with the examples in the entry.
  The rows must be nondecreasing from top to bottom, the columns from left to right.
* A 2 X 2 subblock consists of two adjacent rows and two adjacent columns. Two subblocks are
  horizontal (resp. vertical) neighbors when one is shifted by one column (resp. one row)
  from the other; their sums may differ by at most one.
* The generating function is that of the sequence from offset 1: the coefficient of `X ^ 0` is
  set to `0`, and the identity is multiplied out by `(1 - X) ^ 4` in `ℤ⟦X⟧`.
-/

namespace OMA.S_oeis_a184064

/-- Row `i` of `A`, read from left to right. -/
def row {n : ℕ} (A : Fin (n + 1) → Fin 3 → Bool) (i : Fin (n + 1)) : List (Bool) :=
  List.ofFn (A i)

/-- Column `j` of `A`, read from top to bottom. -/
def col {n : ℕ} (A : Fin (n + 1) → Fin 3 → Bool) (j : Fin 3) : List (Bool) :=
  List.ofFn (fun i => A i j)

/-- The rows are in lexicographically nondecreasing order from top to bottom. -/
def RowsNondecreasing {n : ℕ} (A : Fin (n + 1) → Fin 3 → Bool) : Prop :=
  ∀ i : Fin n, row A i.castSucc ≤ row A i.succ

/-- The columns are in lexicographically nondecreasing order from left to right. -/
def ColsNondecreasing {n : ℕ} (A : Fin (n + 1) → Fin 3 → Bool) : Prop :=
  ∀ j : Fin 2, col A j.castSucc ≤ col A j.succ

/-- The sum of the 2 X 2 subblock in rows `i`, `i + 1` and columns `j`, `j + 1`. -/
def subblockSum {n : ℕ} (A : Fin (n + 1) → Fin 3 → Bool) (i : Fin n) (j : Fin 2) : ℕ :=
  (A i.castSucc j.castSucc).toNat + (A i.castSucc j.succ).toNat +
    (A i.succ j.castSucc).toNat + (A i.succ j.succ).toNat

/-- The subblocks `p` and `q` (given by their top-left corners) are horizontal or vertical
neighbors, `q` lying one column to the right of, or one row below, `p`. -/
def Neighbors {n : ℕ} (p q : Fin n × Fin 2) : Prop :=
  (p.1 = q.1 ∧ p.2.val + 1 = q.2.val) ∨ (p.1.val + 1 = q.1.val ∧ p.2 = q.2)

/-- No subblock sum differs from a horizontal or vertical neighbor subblock sum by more
than one. -/
def SmoothSubblocks {n : ℕ} (A : Fin (n + 1) → Fin 3 → Bool) : Prop :=
  ∀ p q : Fin n × Fin 2, Neighbors p q →
    subblockSum A p.1 p.2 ≤ subblockSum A q.1 q.2 + 1 ∧
      subblockSum A q.1 q.2 ≤ subblockSum A p.1 p.2 + 1

/-- The arrays counted by A184064. -/
def IsValid {n : ℕ} (A : Fin (n + 1) → Fin 3 → Bool) : Prop :=
  RowsNondecreasing A ∧ ColsNondecreasing A ∧ SmoothSubblocks A

/-- `a n` is the number of valid (n+1) X 3 binary arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin (n + 1) → Fin 3 → Bool // IsValid A}

open PowerSeries in
/-- Colin Barker's conjectures for A184064: the generating function, the closed form and the
recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 4 =
      X * (11 - 28 * X + 38 * X ^ 2 - 19 * X ^ 3 + 5 * X ^ 4 - X ^ 5 + 2 * X ^ 6) ∧
    (∀ n : ℕ, 3 < n → 3 * (a n : ℤ) = 4 * n ^ 3 - 15 * n ^ 2 + 74 * n - 93) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a184064
