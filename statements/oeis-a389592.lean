import Mathlib

/-!
# A389592: Irregular triangle read by rows: T(n,k) is the sum of the numbers that are not the smallest number in the k-th 2-dense sublist of divisors of n, with n >= 1, k >= 1.

Source: https://oeis.org/A389592
Credit: @esracummings31-blip

Conjecture (OEIS): T(n,k) = A384149(n,k) - A379288(n,k).

Conventions.
* The 2-dense sublists of divisors of `n`: list the divisors of `n` in increasing order and cut
  between adjacent divisors `d < e` exactly when `e > 2*d` (maximal sublists whose adjacent
  terms differ by a factor `≤ 2`). Rows are indexed by `k`, 0-indexed here (OEIS: k ≥ 1).
* A384149(n,k) is the sum of the k-th 2-dense sublist (the 2-densely-aggregated composition).
* Row `n` of A379288 lists, in increasing order, the odd divisors `e` of `n` for which there is
  no divisor `j` of `n` with `j < e < 2*j`; `A379288 n k` is its k-th term (0-indexed; `0` if
  the row is too short).
* The identity is stated for every row `n ≥ 1` and every `k` indexing a 2-dense sublist.
-/

namespace OMA.S_oeis_a389592

/-- The 2-dense sublists of the divisors of `n`. -/
def blocks (n : ℕ) : List (List ℕ) :=
  (n.divisors.sort (· ≤ ·)).splitBy (fun d e => decide (e ≤ 2 * d))

/-- The k-th 2-dense sublist (empty if out of range). -/
def blk (n k : ℕ) : List ℕ := ((blocks n)[k]?).getD []

/-- A389592(n,k): sum of the terms of the k-th sublist that are not its smallest term. -/
def T (n k : ℕ) : ℕ := ((blk n k).filter (fun x => decide (∃ y ∈ blk n k, y < x))).sum

/-- A384149(n,k): sum of the k-th 2-dense sublist. -/
def A384149 (n k : ℕ) : ℕ := (blk n k).sum

/-- Row `n` of A379288. -/
def row379288 (n : ℕ) : List ℕ :=
  (n.divisors.filter (fun e => Odd e ∧ ¬ ∃ j ∈ n.divisors, j < e ∧ e < 2 * j)).sort (· ≤ ·)

/-- A379288(n,k). -/
def A379288 (n k : ℕ) : ℕ := ((row379288 n)[k]?).getD 0

theorem main : ∀ n : ℕ, 1 ≤ n → ∀ k < (blocks n).length,
    T n k = A384149 n k - A379288 n k := by
  sorry

end OMA.S_oeis_a389592
