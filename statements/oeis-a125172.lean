import Mathlib

/-!
# A125172: Triangle T(n,k) with partial column sums of the even-indexed Fibonacci numbers

Source: https://oeis.org/A125172
Credit: @timlantin

The formula section of the entry reads

  T(n,1) = A001906(n).
  T(n,k) = T(n-1,k-1) + T(n-1,k), k > 1.
  From R. J. Mathar, Sep 06 2011:
  T(n,k) = A125171(n,k), i.e., A125171 without column k=0.
  Conjecture: T(n,k) = T(n,k-1) - A121460(n+1,k).

`A001906(n)` is the Fibonacci number `F(2n)`. The triangle has `1 <= k <= n` (offset 1; rows
1; 3, 1; 8, 4, 1; 21, 12, 5, 1; ...). A121460 (https://oeis.org/A121460, offset 1, `1 <= k <= n`)
is: "Triangle read by rows: T(n,k) is the number of nondecreasing Dyck paths of semilength n,
having k returns to the x-axis", where a Dyck path is nondecreasing when the altitudes of its
valleys, read from left to right, form a nondecreasing sequence (example of the entry: UUDUDDUD
"is not nondecreasing since its valleys are at altitudes 1 and 0"). It is defined here by this
combinatorial description, not by the formula given in that entry.

Range. The conjecture involves `T(n,k-1)`, so it is stated for the entries of the triangle with
`k >= 2`, that is for `2 <= k <= n`; then `A121460(n+1,k)` is an entry of its triangle as well.
With the offsets of the two entries the line holds on the data as written (for instance
`T(3,2) = 4 = T(3,1) - A121460(4,2) = 8 - 4`), so no shift of index is made. The identity is
stated in `ℤ`, so that the subtraction is the true one.

Conventions. Dyck paths are Mathlib's `DyckWord` (`U` an up step, `D` a down step). In the
recurrence at `k = n` the term `T(n-1,n)` lies outside the triangle; it is `0` ("partial column
sums": column `k` consists of the partial sums of column `k-1`), which is what the definition
of `T` below gives outside the triangle.
-/

namespace OMA.S_oeis_a125172

open DyckStep

/-- The triangle A125172: `T(n,1) = F(2n)` and `T(n,k) = T(n-1,k-1) + T(n-1,k)` for `k > 1`,
with value `0` outside `1 ≤ k ≤ n`. -/
def T : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k =>
    if k = 0 then 0 else if k = 1 then Nat.fib (2 * (n + 1)) else T n (k - 1) + T n k

/-- The altitudes of the valleys of a path, read from left to right. A valley is a `D` step
immediately followed by a `U` step, and its altitude is the height of the path between these
two steps. Here `l` is the part of the path still to be read, `h` the height at which it
starts and `prev` the step just before it. -/
def valleyAltitudes : DyckStep → ℤ → List DyckStep → List ℤ
  | _, _, [] => []
  | prev, h, U :: l => (if prev = D then [h] else []) ++ valleyAltitudes U (h + 1) l
  | _, h, D :: l => valleyAltitudes D (h - 1) l

/-- A Dyck path is nondecreasing when the altitudes of its valleys form a nondecreasing
sequence from left to right. (The path starts at height `0`; the initial `prev = U` means that
there is no valley at the starting point.) -/
def IsNondecreasing (p : DyckWord) : Prop :=
  (valleyAltitudes U 0 p.toList).Pairwise (· ≤ ·)

/-- The number of steps of `l`, a path starting at height `h`, that end at height `0`. -/
def returnsFrom : ℤ → List DyckStep → ℕ
  | _, [] => 0
  | h, U :: l => (if h + 1 = 0 then 1 else 0) + returnsFrom (h + 1) l
  | h, D :: l => (if h - 1 = 0 then 1 else 0) + returnsFrom (h - 1) l

/-- The number of returns of a Dyck path to the x-axis. -/
def returns (p : DyckWord) : ℕ := returnsFrom 0 p.toList

/-- A121460: the number of nondecreasing Dyck paths of semilength `n` with `k` returns to the
x-axis. -/
noncomputable def A121460 (n k : ℕ) : ℕ :=
  Set.ncard {p : DyckWord | p.semilength = n ∧ IsNondecreasing p ∧ returns p = k}

theorem main : ∀ n k : ℕ, 2 ≤ k → k ≤ n →
    (T n k : ℤ) = (T n (k - 1) : ℤ) - (A121460 (n + 1) k : ℤ) := by
  sorry

end OMA.S_oeis_a125172
