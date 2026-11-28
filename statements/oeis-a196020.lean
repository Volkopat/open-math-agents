import Mathlib

/-!
# A196020: Irregular triangle read by rows: T(n,k), n >= 1, k >= 1, in which column k lists the
odd numbers interleaved with k-1 zeros, and the first element of column k is in row k(k+1)/2.

Source: https://oeis.org/A196020
Credit: @esracummings31-blip

Conjecture (Omar E. Pol, Feb 14 2018): T(n,k) is the difference between the square of the total
number of partitions of all positive integers <= n into exactly k consecutive parts, and the square
of the total number of partitions of all positive integers < n into exactly k consecutive parts.

Conventions.
* Row n has the entries T(n,k) for 1 <= k with k(k+1)/2 <= n (row length A003056(n)).
* Column k, read from row k(k+1)/2 downward, is 1, 0, ..., 0 (k-1 zeros), 3, 0, ..., 0, 5, ...:
  T(n,k) = 2t+1 when n = k(k+1)/2 + k*t, and 0 otherwise.
* A partition of m into exactly k consecutive parts is determined by its smallest part a >= 1, with
  a + (a+1) + ... + (a+k-1) = m; necessarily a <= m.
-/

namespace OMA.S_oeis_a196020

/-- The triangle A196020. -/
def T (n k : ℕ) : ℕ :=
  if k * (k + 1) / 2 ≤ n ∧ k ∣ n - k * (k + 1) / 2 then 2 * ((n - k * (k + 1) / 2) / k) + 1 else 0

/-- Number of partitions of m into exactly k consecutive parts. -/
def consecParts (m k : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter (fun a => ∑ i ∈ Finset.range k, (a + i) = m)).card

/-- Total number of partitions of all positive integers <= n into exactly k consecutive parts. -/
def P (n k : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 n, consecParts m k

theorem main : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → k * (k + 1) / 2 ≤ n →
    (T n k : ℤ) = (P n k : ℤ) ^ 2 - (P (n - 1) k : ℤ) ^ 2 := by
  sorry

end OMA.S_oeis_a196020
