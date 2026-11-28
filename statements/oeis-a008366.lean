import Mathlib

/-!
# A008366: Smallest prime factor is >= 17.

Source: https://oeis.org/A008366
Credit: @eltociear

A008366 lists the 17-rough numbers: the positive integers with no prime factor less than 17
(`1, 17, 19, 23, ...`). The entry's formula section records the following conjecture
(Gary Detlefs, Dec 27 2011):

  A008366 = numbers `n > 1` such that `(Sum_{k=1..n} k^10) mod n = 0` and
  `(Sum_{k=1..n} k^12) mod n = 0`.

Since the characterisation is stated for `n > 1`, it is read as: for every `n > 1`, `n` divides
both power sums exactly when `n` is a term of A008366. For `n > 1`, being a term means that the
smallest prime factor `Nat.minFac n` is at least `17` (`Nat.minFac n` is the least prime factor of
`n` when `n ≠ 1`). The term `1` lies outside the conjecture's range `n > 1` and is not part of the
statement.
-/

namespace OMA.S_oeis_a008366

/-- Detlefs' conjecture in OEIS A008366: for `n > 1`, `n` divides both `∑_{k=1}^n k^10` and
`∑_{k=1}^n k^12` if and only if the smallest prime factor of `n` is at least `17`. -/
theorem main : ∀ n : ℕ, 1 < n →
    ((n ∣ ∑ k ∈ Finset.Icc 1 n, k ^ 10 ∧ n ∣ ∑ k ∈ Finset.Icc 1 n, k ^ 12) ↔
      17 ≤ Nat.minFac n) := by
  sorry

end OMA.S_oeis_a008366
-- ci: re-run check-proof
