import Mathlib

/-!
# A019338: Primes with primitive root 8

Source: https://oeis.org/A019338
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Artin's conjecture for 8):
Let `a(n)` be the `n`-th prime with primitive root `8`, and let `A` be Artin's constant
`∏_{p prime} (1 - 1 / (p * (p - 1)))`.
Then `a(n) ~ (5 / (3 * A)) * n * log(n)` as `n → ∞`.

Conventions:
- `8` is a primitive root modulo prime `p` iff `orderOf (8 : ZMod p) = p - 1`.
- `aSeq n` is `Nat.nth (fun p => Nat.Prime p ∧ orderOf (8 : ZMod p) = p - 1) n`.
-/

namespace OMA.S_oeis_a019338

noncomputable def artinConst : ℝ :=
  ∏' p : {p : ℕ // Nat.Prime p}, (1 - 1 / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)))

noncomputable def aSeq (n : ℕ) : ℕ :=
  Nat.nth (fun p => Nat.Prime p ∧ orderOf (8 : ZMod p) = p - 1) n

theorem main :
    Filter.Tendsto
      (fun n : ℕ => (aSeq n : ℝ) / ((5 / (3 * artinConst)) * (n : ℝ) * Real.log (n : ℝ)))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a019338
