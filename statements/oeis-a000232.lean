import Mathlib

/-!
# A000232: Construct a triangle as in A036262. Sequence is one less than the position of the first number larger than 2 in the n-th row (n-th difference).

Source: https://oeis.org/A000232
Credit: @luciusacarr

The entry (data 3, 8, 14, 14, 25, 24, 23, 22, 25, 59, ..., offset 1) records the claim
(Bartlomiej Pawlik, Nov 28 2025): if a(n) > 2 for every n, then the Gilbreath conjecture is true.

Reading of the source:
* A036262 is the Gilbreath array: row 0 lists the primes, T(0, k) = prime(k) for k >= 1 (so
  T(0, 1) = 2), and T(n, k) = |T(n-1, k+1) - T(n-1, k)| for n >= 1. In Lean the k-th prime is
  `Nat.nth Nat.Prime (k - 1)`; the unused column k = 0 is irrelevant.
* Positions in a row are 1-indexed (row 1 is 1, 2, 2, 4, ..., its first entry > 2 is at position 4,
  and a(1) = 3). So a(n) = (least k >= 1 with T(n, k) > 2) - 1, for n >= 1; here the least such k
  is `sInf` of the set (which would be 0 if no such entry existed, making a(n) = 0).
* The Gilbreath conjecture: for every n >= 1, the first entry T(n, 1) of row n equals 1.
* The claim: if 2 < a(n) for every n >= 1, then T(n, 1) = 1 for every n >= 1.
-/

namespace OMA.S_oeis_a000232

/-- The Gilbreath array A036262: row 0 lists the primes, `T 0 k = prime(k)` (1-indexed, so
`T 0 1 = 2`), and each later row is the absolute value of the differences of the previous one. -/
noncomputable def T : ℕ → ℕ → ℤ
  | 0, k => (Nat.nth Nat.Prime (k - 1) : ℤ)
  | n + 1, k => |T n (k + 1) - T n k|

/-- `a n` is one less than the (1-indexed) position of the first entry larger than 2 in row `n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ 2 < T n k} - 1

theorem main : (∀ n, 1 ≤ n → 2 < a n) → ∀ n, 1 ≤ n → T n 1 = 1 := by
  sorry

end OMA.S_oeis_a000232
