import Mathlib

/-!
# OEIS A000961: powers of primes, a power-sum characterisation

Source: https://oeis.org/A000961
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A000961 is `1` together with the prime powers `p^k` (`k ≥ 1`). Conjecture (Ordowski and Resta,
2018): these are exactly the positive integers `m` with
`∑_{k=0}^{m-1} k^φ(m) ≡ φ(m) (mod m)`.

Conventions:
* `m` ranges over positive integers; `0^0 = 1` as in Lean (only relevant for `m = 1`, where
  every residue is `0` mod `1`).
-/

namespace OMA.S_oeis_a000961

/-- `m` is a term of A000961. -/
def InA000961 (m : ℕ) : Prop := m = 1 ∨ IsPrimePow m

/-- Terms of A000961 are exactly the `m ≥ 1` with `∑_{k<m} k^φ(m) ≡ φ(m) (mod m)`. -/
theorem main : ∀ m : ℕ, 0 < m →
    (InA000961 m ↔ (∑ k ∈ Finset.range m, k ^ Nat.totient m) % m = Nat.totient m % m) := by
  sorry

end OMA.S_oeis_a000961
