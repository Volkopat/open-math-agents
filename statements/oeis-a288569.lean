import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Count
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a288569

/-- OEIS A087207: binary representation of the distinct prime factors of `n`,
given by `∑_{p ∈ n.primeFactors} 2^(π(p) - 1)`, where `Nat.count Nat.Prime p`
equals `π(p) - 1` for every prime `p`. -/
def a087207 (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, 2 ^ (Nat.count Nat.Prime p)

/-- Predicate stating that starting from `n` and repeatedly applying `a087207`
reaches `0` for the first time in exactly `t` steps. -/
def ReachesZeroIn (n t : ℕ) : Prop :=
  a087207^[t] n = 0 ∧ ∀ s < t, a087207^[s] n ≠ 0

/-- OEIS A288569 Conjectures 2, 3, and 4 (Bill McEachen, Sep 04 2026):
- Conjecture 2: `a(2^k) = 2` for every `k ≥ 1`.
- Conjecture 3: `a(p) = 3` for every odd prime `p`.
- Conjecture 4: if `n` is an odd composite integer and iterating `a087207` from `n`
  reaches `0` in `t` steps, then `t` is odd. -/
theorem main :
    (∀ k : ℕ, 1 ≤ k → ReachesZeroIn (2 ^ k) 2) ∧
    (∀ p : ℕ, p.Prime → Odd p → ReachesZeroIn p 3) ∧
    (∀ n t : ℕ, 1 < n → Odd n → ¬ n.Prime → ReachesZeroIn n t → Odd t) := by
  sorry

end OMA.S_oeis_a288569
