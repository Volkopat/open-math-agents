import Mathlib

/-!
# OEIS A068192: Recursive Sequence f(n) - prevprime(f(n) - 1) Consists Only of Primes

Source: https://oeis.org/A068192
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Define $a(1) = 2$, and for $n \ge 2$ define
$$f(n) = 4 \prod_{i=1}^{n-1} a(i), \qquad a(n) = f(n) - \mathrm{prevprime}(f(n) - 1),$$
where $\mathrm{prevprime}(x)$ is the largest prime $< x$ (so $a(2) = 8 - 5 = 3$).

Conjecture: Every term $a(n)$ ($n \ge 1$) is prime.
-/

namespace OMA.S_oeis_a068192

/-- Largest prime `< x` (or `0` if `x ≤ 2`). -/
noncomputable def prevPrime (x : ℕ) : ℕ :=
  sSup {p : ℕ | p < x ∧ Nat.Prime p}

/-- The sequence `a` (0-indexed: `aSeq 0 = a(1) = 2`). -/
noncomputable def aSeq : ℕ → ℕ
  | 0 => 2
  | n + 1 =>
      let f := 4 * ∏ i : Fin (n + 1), aSeq i.1
      f - prevPrime (f - 1)
  decreasing_by exact i.isLt

theorem main :
    ∀ n : ℕ, Nat.Prime (aSeq n) := by
  sorry

end OMA.S_oeis_a068192
