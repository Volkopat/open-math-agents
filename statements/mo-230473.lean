import Mathlib

/-!
# How big are the prime factors of 2^k p - 1?

Source: https://mathoverflow.net/questions/230473
Credit: @antonumias24-tech

The question: let `p` be a prime number, `p > 3`. Does there always exist `k ∈ ℕ_{≥ 1}` such
that the prime factors of `2^k p - 1` are all less than `p`?

Translation choices.
* `k` ranges over the natural numbers with `1 ≤ k`, as in the source.
* For `p > 3` and `k ≥ 1`, `2 ^ k * p - 1 ≥ 9`, so the natural-number subtraction does not
  truncate.
* All prime factors are less than `p` is: every prime `q` dividing `2 ^ k * p - 1` satisfies
  `q < p` (strict inequality, as in the source).
* The expected answer is yes: a direct search finds a suitable `k ≤ 5` for every prime
  `3 < p < 3000` (the worst case there is `p = 307`, which needs `k = 5`), so `main` states the
  affirmative answer.
-/

namespace OMA.S_mo_230473

theorem main : ∀ p : ℕ, p.Prime → 3 < p →
    ∃ k : ℕ, 1 ≤ k ∧ ∀ q : ℕ, q.Prime → q ∣ 2 ^ k * p - 1 → q < p := by
  sorry

end OMA.S_mo_230473
