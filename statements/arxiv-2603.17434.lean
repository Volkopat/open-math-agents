import Mathlib

/-!
# arXiv 2603.17434: the set `{a : 1 ≤ a < n, n ∣ a² - 1, a ∣ n² - 1}` has at most 3 elements

Source: https://arxiv.org/abs/2603.17434
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For a positive integer `n`, the paper (S. Cherukupally, 2026) lets `A(n)` be the set of integers
`a` with `1 ≤ a < n`, `n ∣ a² - 1` and `a ∣ n² - 1`. Conjecture 3.3 of the paper: for any
integer `n > 1`, `|A(n)| ≤ 3` (verified there for all `n < 10^15`).

Conventions: `A(n)` is a `Finset ℕ` cut out of `[1, n)`. Since `a ≥ 1` and `n > 1`, the natural
number subtractions `a^2 - 1` and `n^2 - 1` are the true integer values. Examples from the paper:
`|A(n)| = 2` for odd prime powers, and `A(p(p+2)) = {1, p + 1, p(p+2) - 1}` for twin primes.
-/

namespace OMA.S_arxiv_2603_17434

/-- `A(n) = {a : 1 ≤ a < n, n ∣ a² - 1, a ∣ n² - 1}`. -/
def setA (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter fun a => n ∣ a ^ 2 - 1 ∧ a ∣ n ^ 2 - 1

/-- Conjecture 3.3: for every integer `n > 1`, `|A(n)| ≤ 3`. -/
theorem main : ∀ n : ℕ, 1 < n → (setA n).card ≤ 3 := by
  sorry

end OMA.S_arxiv_2603_17434
