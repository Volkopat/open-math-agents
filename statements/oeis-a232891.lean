import Mathlib

/-!
# A232891: Least positive integer m <= n^2/2 + 3 such that {k*prime(k): k = 1,...,m} contains a complete system of residues modulo n, or 0 if such a number m does not exist.

Source: https://oeis.org/A232891
Credit: @keiichisince1986-bot

A232891 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0.
(ii) For any positive integer n not equal to 3, the number n*prime(n) + 1 cannot be a power x^m with
m > 1.

Conventions:
- `prime(m)` is the `m`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (m - 1)` (Mathlib's
  `Nat.nth Nat.Prime` counts from `0`).
- (i): `a(n) > 0` means that some `m ≤ n^2/2 + 3` has every residue `r` modulo `n` among the values
  `k * prime(k)` with `1 ≤ k ≤ m`; equivalently, every `r < n` is `(k * prime(k)) mod n` for some
  `1 ≤ k ≤ n^2/2 + 3`. For an integer `k`, `k ≤ n^2/2 + 3` is the same as `2k ≤ n^2 + 6`.
- (ii): a power `x^m` with `m > 1` (and natural `x`); since `n * prime(n) + 1 ≥ 3`, necessarily `x ≥ 2`.
  For `n = 3`, `3 * 5 + 1 = 2^4`.
- Both parts are formalized, as a conjunction.
-/

namespace OMA.S_oeis_a232891

theorem main :
    (∀ n : ℕ, 0 < n → ∀ r : ℕ, r < n → ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ n ^ 2 + 6 ∧
        (k * Nat.nth Nat.Prime (k - 1)) % n = r) ∧
      ∀ n : ℕ, 0 < n → n ≠ 3 → ¬ ∃ x m : ℕ, 1 < m ∧ n * Nat.nth Nat.Prime (n - 1) + 1 = x ^ m := by
  sorry

end OMA.S_oeis_a232891
