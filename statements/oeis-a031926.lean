import Mathlib

/-!
# OEIS A031926: primes followed by a gap of 8, a Firoozbakht-type conjecture

Source: https://oeis.org/A031926
`a n` is the lower prime of a difference of `8` between consecutive primes
(89, 359, 389, …). Conjecture (Kholdi–Firoozbakht): the sequence is infinite and
`a(n+1) < a(n)^(1 + 1/n)` for every `n`, i.e. `a(n)^(1/n)` is strictly decreasing.

Conventions. Offset `1`: `a n = Nat.nth P (n - 1)` where `P p` says that `p` and `p + 8` are
consecutive primes.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a031926

/-- `p` and `p + 8` are consecutive primes. -/
def P (p : ℕ) : Prop := p.Prime ∧ (p + 8).Prime ∧ ∀ q, p < q → q < p + 8 → ¬ q.Prime

/-- A031926, indexed from `1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

theorem main :
    {p : ℕ | P p}.Infinite ∧
      ∀ n : ℕ, 1 ≤ n → (a (n + 1) : ℝ) < (a n : ℝ) ^ (1 + 1 / (n : ℝ)) := by
  sorry

end OMA.S_oeis_a031926
