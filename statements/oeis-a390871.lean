import Mathlib

/-!
# A390871: Numbers k >= 1 such that k^2 - r^2 = 2^m - 1 for some 0 <= m <= k and 0 <= r < k

Source: https://oeis.org/A390871
Credit: @xor2k

Formalizes the OEIS A390871 conjecture: For k != A000079(n), if there is a solution for k > 8,
then m is from [A000523(k) + 3, 2*A000523(k) + 1] (I conjecture).

Conventions:
- A000079 is the powers of two `2^n`, `n ≥ 0`; `k != A000079(n)` means `k` is not a power of two.
- A000523(k) is `floor(log_2 k)`, which is `Nat.log 2 k`.
- A solution for `k` is a pair `(m, r)` of naturals with `m ≤ k`, `r < k` and
  `k^2 - r^2 = 2^m - 1` (natural subtraction, exact here since `r < k` and `2^m ≥ 1`).
- The claim: for every `k > 8` that is not a power of two, every solution `(m, r)` has
  `A000523(k) + 3 ≤ m ≤ 2*A000523(k) + 1`.
-/

namespace OMA.S_oeis_a390871

/-- For `k > 8` not a power of two, every solution of `k^2 - r^2 = 2^m - 1` with `m ≤ k` and
`r < k` has `floor(log_2 k) + 3 ≤ m ≤ 2 floor(log_2 k) + 1`. -/
theorem main :
    ∀ k : ℕ, 8 < k → (¬ ∃ n : ℕ, k = 2 ^ n) →
      ∀ m r : ℕ, m ≤ k → r < k → k ^ 2 - r ^ 2 = 2 ^ m - 1 →
        Nat.log 2 k + 3 ≤ m ∧ m ≤ 2 * Nat.log 2 k + 1 := by
  sorry

end OMA.S_oeis_a390871
