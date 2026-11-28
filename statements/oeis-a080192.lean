import Mathlib

/-!
# OEIS A080192: primes with no prime between 2p and 2p'

Source: https://oeis.org/A080192
`A080192` is the complement of A080191 in the primes: a prime `p` is a term iff there is no
prime between `2p` and `2q`, where `q` is the next prime after `p`. Conjecture:
`a(n) / prime(n) → 3`.

Conventions. "Between" is strict: no prime `r` with `2p < r < 2q`. Both sequences are indexed
from `1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a080192

open Filter Topology

/-- `p` is prime and no prime lies strictly between `2p` and twice the next prime. -/
def P (p : ℕ) : Prop :=
  p.Prime ∧ ∀ q : ℕ, q.Prime → p < q → (∀ r, p < r → r < q → ¬ r.Prime) →
    ∀ r, 2 * p < r → r < 2 * q → ¬ r.Prime

theorem main :
    Tendsto (fun n : ℕ => (Nat.nth P n : ℝ) / Nat.nth Nat.Prime n) atTop (𝓝 3) := by
  sorry

end OMA.S_oeis_a080192
