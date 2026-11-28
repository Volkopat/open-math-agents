import Mathlib

/-!
# A234808: a(n) = |{0 < k < n: p = k + phi(n-k) and 2*n - p are both prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234808
Credit: @keiichisince1986-bot

A234808 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 except for n = 1, 8.

Conventions:
- `phi` is `Nat.totient`. For `0 < k < n` we have `p = k + phi(n - k) ≤ k + (n - k) = n < 2n`, so the
  natural-number subtractions `n - k` and `2n - p` are exact.
- The conjecture says that, among `n ≥ 1`, `a(n) = 0` holds exactly for `n = 1` and `n = 8` (both
  values are `0` in the data): the set of `n > 0` for which no such `k` exists is `{1, 8}`.
-/

namespace OMA.S_oeis_a234808

theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ k : ℕ, 0 < k ∧ k < n ∧ (k + Nat.totient (n - k)).Prime ∧
        (2 * n - (k + Nat.totient (n - k))).Prime} = {1, 8} := by
  sorry

end OMA.S_oeis_a234808
