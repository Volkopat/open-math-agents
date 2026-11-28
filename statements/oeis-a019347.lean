import Mathlib

/-!
# A019347: Primes with primitive root 20

Source: https://oeis.org/A019347
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture (Artin's conjecture for 20):
The number of primes `p ≤ N` having `20` as a primitive root is asymptotically equivalent to
`(20 / 19) * C * primepi(N)` as `N → ∞`, where `C = ∏_{p prime} (1 - 1 / (p * (p - 1)))`
is Artin's constant.

Conventions:
- `20` is a primitive root modulo prime `p` iff `orderOf (20 : ZMod p) = p - 1`.
-/

namespace OMA.S_oeis_a019347

noncomputable def artinConst : ℝ :=
  ∏' p : {p : ℕ // Nat.Prime p}, (1 - 1 / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)))

noncomputable def primePi (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter Nat.Prime).card

noncomputable def countPrimRoot20 (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun p =>
    Nat.Prime p ∧ orderOf (20 : ZMod p) = p - 1).card

theorem main :
    Filter.Tendsto
      (fun N : ℕ => (countPrimRoot20 N : ℝ) / ((20 / 19 : ℝ) * artinConst * (primePi N : ℝ)))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a019347
