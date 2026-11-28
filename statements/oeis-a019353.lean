import Mathlib

/-!
# A019353: Primes with primitive root 27

Source: https://oeis.org/A019353
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Artin's conjecture for 27):
The number of primes `p ≤ N` having `27` as a primitive root is asymptotically equivalent to
`(3 / 5) * C * primepi(N)` as `N → ∞`, where `C = ∏_{p prime} (1 - 1 / (p * (p - 1)))`
is Artin's constant.

Conventions:
- `27` is a primitive root modulo prime `p` iff `orderOf (27 : ZMod p) = p - 1`.
-/

namespace OMA.S_oeis_a019353

noncomputable def artinConst : ℝ :=
  ∏' p : {p : ℕ // Nat.Prime p}, (1 - 1 / ((p.1 : ℝ) * ((p.1 : ℝ) - 1)))

noncomputable def primePi (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter Nat.Prime).card

noncomputable def countPrimRoot27 (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter fun p =>
    Nat.Prime p ∧ orderOf (27 : ZMod p) = p - 1).card

theorem main :
    Filter.Tendsto
      (fun N : ℕ => (countPrimRoot27 N : ℝ) / ((3 / 5 : ℝ) * artinConst * (primePi N : ℝ)))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a019353
