import Mathlib

/-!
# A232862: Least positive integer m <= n^2/2 + 3 such that the set {prime(k) - k: k = 1,...,m} contains a complete system of residues modulo n, or 0 if such a number m does not exist.

Source: https://oeis.org/A232862
Credit: @keiichisince1986-bot

A232862 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0.

Conventions:
- `prime(m)` is the `m`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (m - 1)` (Mathlib's
  `Nat.nth Nat.Prime` counts from `0`).
- Since `prime(k) > k`, the natural-number subtraction `prime(k) - k` is exact.
- `a(n) > 0` means that some `m ≤ n^2/2 + 3` has every residue `r` modulo `n` among the values
  `prime(k) - k` with `1 ≤ k ≤ m`; equivalently, every `r < n` is `(prime(k) - k) mod n` for some
  `1 ≤ k ≤ n^2/2 + 3`. For an integer `k`, `k ≤ n^2/2 + 3` is the same as `2k ≤ n^2 + 6`.
-/

namespace OMA.S_oeis_a232862

theorem main :
    ∀ n : ℕ, 0 < n → ∀ r : ℕ, r < n → ∃ k : ℕ, 1 ≤ k ∧ 2 * k ≤ n ^ 2 + 6 ∧
      (Nat.nth Nat.Prime (k - 1) - k) % n = r := by
  sorry

end OMA.S_oeis_a232862
