import Mathlib

/-!
# OEIS A090920: n followed by the least k ≡ 1 (mod n)

Source: https://oeis.org/A090920
`a n` is the prime formed by `n` followed by the least `k ≡ 1 (mod n)` making the concatenation
prime. Conjecture: for `n > 1`, if `a(n)` is `n` concatenated with `k`, then `k < n²`.

Conventions. Concatenation is decimal: `n` followed by `k` is `n · 10^(digits of k) + k`
(`k ≥ 1`, no leading zeros). `main` states: for `n > 1` there is `k ≡ 1 (mod n)` with `k < n²`
whose concatenation with `n` is prime (equivalently, the least such `k` is `< n²`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a090920

/-- Decimal concatenation of `n` and `k`. -/
def concat (n k : ℕ) : ℕ := n * 10 ^ (Nat.digits 10 k).length + k

theorem main :
    ∀ n : ℕ, 1 < n → ∃ k : ℕ, 1 ≤ k ∧ k % n = 1 ∧ k < n ^ 2 ∧ (concat n k).Prime := by
  sorry

end OMA.S_oeis_a090920
