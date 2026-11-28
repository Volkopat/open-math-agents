import Mathlib

/-!
# A327433: Smallest k > 2 such that the k-th complementary Bell number is divisible by n

Source: https://oeis.org/A327433

Conjecture (OEIS A327433):
For every positive integer `n`, there exists `k > 2` such that `n` divides the `k`-th
Rao Uppuluri-Carpenter (complementary Bell) number `A000587(k) = ∑_{j=0}^k (-1)^j S(k, j)`,
where `S(k, j)` denotes the Stirling number of the second kind.

Conventions:
- Offset: `1`; first terms of A000587 (`k ≥ 0`): `1, -1, 0, 1, 1, -2, -9, -9, 50, ...`.
- First terms of A327433 (`n ≥ 1`): `3, 5, 6, 11, 8, 20, 10, 14, 6, 8, 14, 35, ...`.
- Note `A000587(2) = 0`, which is why the condition requires `k > 2`.
-/

namespace OMA.S_oeis_a327433

/-- Stirling numbers of the second kind `S(n, k)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- The `k`-th complementary Bell (Rao Uppuluri-Carpenter) number (OEIS A000587). -/
def compBell (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (stirling2 k j : ℤ)

/-- Conjecture: for every `n ≥ 1`, there exists `k > 2` such that `n ∣ A000587(k)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 2 < k ∧ (n : ℤ) ∣ compBell k := by
  sorry

end OMA.S_oeis_a327433
