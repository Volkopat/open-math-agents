import Mathlib

/-!
# A019334: Primes with primitive root 3 (Artin's conjecture and mod 12 distribution)

Source: https://oeis.org/A019334
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

## Problem Statement
Let `A019334` be the sequence of primes `p` having `3` as a primitive root modulo `p`, and let
`C = ∏_{p prime} (1 - 1 / (p * (p - 1)))` be Artin's constant (A005596).
Define:
- `Q(N) = #{p prime : 2 < p ≤ N, 3 is a primitive root mod p}`,
- `Q(N, b) = #{p prime : p ≤ N, p ≡ b (mod 12), 3 is a primitive root mod p}`.

Conjecture (Artin's conjecture for base 3 and its mod 12 bias):
As `N → ∞`,
- `Q(N) ~ C * N / log(N)`,
- `Q(N, 5) ~ (3 / 5) * Q(N)`,
- `Q(N, 7) ~ (2 / 5) * Q(N)`.
-/

namespace OMA.S_oeis_a019334

/-- Artin's constant `C = ∏_{p prime} (1 - 1 / (p * (p - 1)))`. -/
noncomputable def artinConstant : ℝ :=
  ∏' p : { p : ℕ // Nat.Prime p }, (1 - 1 / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)))

/-- `p` is a prime with primitive root `3`. -/
def hasPrimRoot3 (p : ℕ) : Prop :=
  Nat.Prime p ∧ orderOf (3 : ZMod p) = p - 1

/-- Count of odd primes `p ≤ N` having primitive root `3`. -/
noncomputable def Q (N : ℕ) : ℕ :=
  Nat.card { p : ℕ // 2 < p ∧ p ≤ N ∧ hasPrimRoot3 p }

/-- Count of primes `p ≤ N` with `p ≡ b (mod 12)` having primitive root `3`. -/
noncomputable def Qb (N b : ℕ) : ℕ :=
  Nat.card { p : ℕ // p ≤ N ∧ p % 12 = b ∧ hasPrimRoot3 p }

theorem main :
    Filter.Tendsto
      (fun N : ℕ => (Q N : ℝ) / (artinConstant * (N : ℝ) / Real.log (N : ℝ)))
      Filter.atTop (nhds 1) ∧
    Filter.Tendsto
      (fun N : ℕ => (Qb N 5 : ℝ) / ((3 / 5 : ℝ) * (Q N : ℝ)))
      Filter.atTop (nhds 1) ∧
    Filter.Tendsto
      (fun N : ℕ => (Qb N 7 : ℝ) / ((2 / 5 : ℝ) * (Q N : ℝ)))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a019334
