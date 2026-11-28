import Mathlib

/-!
# A211343: Triangle read by rows: T(n,k), n >= 1, k >= 1, in which column k lists the positive
integers interleaved with k-1 zeros, and the first element of column k is in row k(k+1)/2.

Source: https://oeis.org/A211343
Credit: @esracummings31-blip

Conjectures (Omar E. Pol, Apr 30 2017):
1. T(n,k) is the smallest part of the partition of n into k consecutive parts, if T(n,k) > 0.
2. The last positive integer in row n is in column A109814(n).

Conventions.
* Row n has the entries T(n,k) for 1 <= k with k(k+1)/2 <= n.
* Column k, read from row k(k+1)/2 downward, is 1, 0, ..., 0 (k-1 zeros), 2, 0, ..., 0, 3, ...:
  T(n,k) = t+1 when n = k(k+1)/2 + k*t, and 0 otherwise.
* "T(n,k) is the smallest part of the partition of n into k consecutive parts" is stated as:
  T(n,k), T(n,k)+1, ..., T(n,k)+k-1 add up to n (so these k consecutive positive integers are that
  partition, and T(n,k) is its smallest part).
* A109814(n) is the largest k such that n is a sum of k consecutive positive integers.
-/

namespace OMA.S_oeis_a211343

/-- The triangle A211343. -/
def T (n k : ℕ) : ℕ :=
  if k * (k + 1) / 2 ≤ n ∧ k ∣ n - k * (k + 1) / 2 then (n - k * (k + 1) / 2) / k + 1 else 0

/-- A109814: largest k such that n is the sum of k consecutive positive integers a, ..., a+k-1
(a <= n; and k <= n since k <= a + ... + (a+k-1)). -/
def A109814 (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => ∃ a < n + 1, 1 ≤ a ∧ ∑ i ∈ Finset.range k, (a + i) = n) n

theorem main :
    (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → k * (k + 1) / 2 ≤ n → 0 < T n k →
      ∑ i ∈ Finset.range k, (T n k + i) = n) ∧
    (∀ n : ℕ, 1 ≤ n →
      1 ≤ A109814 n ∧ A109814 n * (A109814 n + 1) / 2 ≤ n ∧ 0 < T n (A109814 n) ∧
      ∀ k, A109814 n < k → k * (k + 1) / 2 ≤ n → T n k = 0) := by
  sorry

end OMA.S_oeis_a211343
