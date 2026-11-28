import Mathlib

/-!
# A012780: Expansion of e.g.f. arcsin(tan(x)) (odd powers only)

Source: https://oeis.org/A012780
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Let `a(n)` be the integer coefficient of `x^(2*n + 1) / (2*n + 1)!` in the exponential
generating function `arcsin(tan(x))`. Then for every positive integer `k`, the sequence
`{a(n)}` reduced modulo `k` is eventually periodic with period dividing `φ(k)` (Euler's totient).

Conventions:
- `a : ℕ → ℤ` is characterized by `(a n : ℝ) = iteratedDeriv (2 * n + 1) (fun x => Real.arcsin (Real.tan x)) 0`.
- Eventual periodicity modulo `k` with period dividing `φ(k)` is stated as
  `∃ N : ℕ, ∀ n ≥ N, a (n + Nat.totient k) ≡ a n [ZMOD (k : ℤ)]`.
-/

namespace OMA.S_oeis_a012780

theorem main :
    ∀ a : ℕ → ℤ,
      (∀ n : ℕ,
        (a n : ℝ) = iteratedDeriv (2 * n + 1) (fun x => Real.arcsin (Real.tan x)) 0) →
      ∀ k : ℕ, k ≥ 1 →
        ∃ N : ℕ, ∀ n ≥ N, a (n + Nat.totient k) ≡ a n [ZMOD (k : ℤ)] := by
  sorry

end OMA.S_oeis_a012780
