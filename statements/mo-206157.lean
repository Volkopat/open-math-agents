import Mathlib

/-!
# Five halvings after a prime-induced increase

Source: https://mathoverflow.net/questions/206157
Credit: @koolkao

Question (Mirko, MathOverflow 206157, 2015; CC BY-SA 3.0). For every prime `p ≥ 13`, starting with
`n = p^2 - 1`, are there always at least five divisions `n ↦ ⌊n/2⌋` before we reach a prime
again? Let `c(p)` count the number of divisions `n ↦ ⌊n/2⌋` starting with `p^2 - 1` before we
reach a prime. [...] My question is whether `c(p) ≥ 5` whenever `p ≥ 13` is a prime.

`main` states that the answer is yes. A disproof is a prime `p ≥ 13` for which one of the first
four quotients is prime.

Translation choices:
* after `k` divisions starting from `n = p^2 - 1` the current value is `⌊(p^2 - 1)/2^k⌋`, which
  is `(p ^ 2 - 1) / 2 ^ k` in `ℕ` (iterated floor halving is floor division by `2^k`);
* `c(p) ≥ 5` means that no prime is reached after one, two, three or four divisions, that is,
  `(p ^ 2 - 1) / 2 ^ k` is not prime for `1 ≤ k ≤ 4` (the source's examples, such as
  `8 ↦ 4 ↦ 2` giving `c(3) = 2`, count the division that reaches the prime and do not test the
  starting value `p^2 - 1` itself).
-/

namespace OMA.S_mo_206157

/-- For every prime `p ≥ 13`, none of `⌊(p^2 - 1)/2^k⌋`, `1 ≤ k ≤ 4`, is prime. -/
theorem main :
    ∀ p : ℕ, p.Prime → 13 ≤ p → ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ¬ ((p ^ 2 - 1) / 2 ^ k).Prime := by
  sorry

end OMA.S_mo_206157
