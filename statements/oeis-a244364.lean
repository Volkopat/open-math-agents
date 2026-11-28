import Mathlib

namespace OMA.S_oeis_a244364

/-- `endsWithIdenticalDigits N n` means the base-10 representation of `N` has at least `n` digits
and its last `n` decimal digits are all equal to some digit `d < 10`. -/
def endsWithIdenticalDigits (N n : ℕ) : Prop :=
  ∃ d : ℕ, d < 10 ∧ 10 ^ (n - 1) ≤ N ∧ N % 10 ^ n = d * ((10 ^ n - 1) / 9)

/-- `maxIdenticalTrailingDigits m n` means `n` is the largest number of identical decimal digits
that can end `m ^ k` for some positive integer `k`. -/
def maxIdenticalTrailingDigits (m n : ℕ) : Prop :=
  (∃ k : ℕ, 1 ≤ k ∧ endsWithIdenticalDigits (m ^ k) n) ∧
  (∀ t : ℕ, (∃ k : ℕ, 1 ≤ k ∧ endsWithIdenticalDigits (m ^ k) t) → t ≤ n)

/-- Conjecture (OEIS A244364): for every `n > 5`, the least integer `m > 1` such that `n` is the
largest number of identical digits that can end `m ^ k` for a positive integer `k` is
`10 * 2 ^ (n - 1) - 1`. -/
theorem main :
    ∀ n : ℕ, 5 < n →
      maxIdenticalTrailingDigits (10 * 2 ^ (n - 1) - 1) n ∧
      (∀ m : ℕ, 1 < m → maxIdenticalTrailingDigits m n → 10 * 2 ^ (n - 1) - 1 ≤ m) := by
  sorry

end OMA.S_oeis_a244364
