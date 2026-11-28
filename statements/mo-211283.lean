import Mathlib

/-!
# Must the digit sum of n^k decrease infinitely often?

Source: https://mathoverflow.net/questions/211283 (CC BY-SA 3.0).

Let `S(n)` be the sum of the decimal digits of `n`. Question: is it true that for every
(positive) integer `n` which is not a power of `10` there are infinitely many `k` such that
`S(n^k) > S(n^(k+1))`? `main` states the expected yes. Powers of `10` include `10⁰ = 1`;
`n` ranges over positive integers, as in the question.
-/

namespace OMA.S_mo_211283

theorem main : ∀ n : ℕ, 0 < n → (∀ j : ℕ, n ≠ 10 ^ j) →
    Set.Infinite {k : ℕ | (Nat.digits 10 (n ^ (k + 1))).sum < (Nat.digits 10 (n ^ k)).sum} := by
  sorry

end OMA.S_mo_211283
