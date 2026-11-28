import Mathlib

/-!
# OEIS A031928: primes followed by a gap of `10`

Source: https://oeis.org/A031928
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A031928 lists the primes `p` such that the next prime is `p + 10`. Conjecture (Kholdi–Firoozbakht,
2014): the sequence is infinite, and `a(n+1) < a(n)^(1 + 1/n)` for every `n`.

Conventions:
* "Next prime is `p + 10`" means `p + 10` is prime and no prime lies strictly between. Offset `1`:
  `a(n) = Nat.nth P (n - 1)`; `n ≥ 1`.
-/

namespace OMA.S_oeis_a031928

/-- `p` is prime and the next prime is `p + 10`. -/
def P (p : ℕ) : Prop := p.Prime ∧ (p + 10).Prime ∧ ∀ q, p < q → q < p + 10 → ¬ q.Prime

/-- `a(n)`, offset `1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- Infinitely many terms, and `a(n+1) < a(n)^(1 + 1/n)`. -/
theorem main : {p | P p}.Infinite ∧
    ∀ n : ℕ, 1 ≤ n → (a (n + 1) : ℝ) < (a n : ℝ) ^ (1 + 1 / (n : ℝ)) := by
  sorry

end OMA.S_oeis_a031928
