import Mathlib

/-!
# A235919: a(n) = |{0 < k < n - 2: p = prime(k) + phi(n-k)/2, prime(p) - p + 1 and (p^2 - 1)/4 - prime(p) are all prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A235919
Credit: @keiichisince1986-bot

A235919 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 24.

Conventions:
- `prime(m)` is the `m`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (m - 1)`.
- `phi` is `Nat.totient`. For `0 < k < n - 2` we have `n - k ≥ 3`, so `phi(n - k)` is even and `phi(n - k)/2` is
  exact.
- `p` itself must be prime (as in the program). `prime(p) > p`, so `prime(p) - p + 1` is exact; for odd `p`,
  `8` divides `p^2 - 1`, so `(p^2 - 1)/4` is exact.
- As in the program of the entry, a value counts only if it is a positive prime; natural-number
  truncation of a non-positive value gives `0`, and natural division of a non-integer quotient (only for
  `p = 2`) gives a value whose difference truncates to `0`, which is not prime either.
-/

namespace OMA.S_oeis_a235919

theorem main :
    ∀ n : ℕ, 24 < n → ∃ k p : ℕ, 0 < k ∧ k < n - 2 ∧
      p = Nat.nth Nat.Prime (k - 1) + Nat.totient (n - k) / 2 ∧ p.Prime ∧
      (Nat.nth Nat.Prime (p - 1) - p + 1).Prime ∧ ((p ^ 2 - 1) / 4 - Nat.nth Nat.Prime (p - 1)).Prime := by
  sorry

end OMA.S_oeis_a235919
