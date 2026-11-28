import Mathlib

/-!
# A227938: List of those numbers which can be written as x + y + z (x, y, z > 0) such that all the six numbers 6*x-1, 6*y-1, 6*z-1, 6*x*y-1, 6*x*z-1 and 6*y*z-1 are Sophie Germain primes.

Source: https://oeis.org/A227938
Credit: @eltociear

A Sophie Germain prime is a prime `p` with `2p + 1` also prime. The sequence (offset 1) lists in
increasing order the numbers `m = x + y + z` with `x, y, z > 0` such that
`6x - 1`, `6y - 1`, `6z - 1`, `6xy - 1`, `6xz - 1`, `6yz - 1` are all Sophie Germain primes
(`a(1) = 3` from `1 + 1 + 1`, `a(7) = 10` from `1 + 2 + 7`). The entry conjectures (Zhi-Wei Sun):

  a(n) < 2*n for all n > 2.

`a(n)` is `Nat.nth InA227938 (n - 1)` (`Nat.nth` counts from `0`). Since `x, y, z > 0`, every
`6·(…) - 1` is an exact natural-number subtraction.
-/

namespace OMA.S_oeis_a227938

/-- `p` is a Sophie Germain prime: `p` and `2p + 1` are prime. -/
def IsSophieGermain (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/-- `m` is a term of A227938. -/
def InA227938 (m : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ m = x + y + z ∧
    IsSophieGermain (6 * x - 1) ∧ IsSophieGermain (6 * y - 1) ∧ IsSophieGermain (6 * z - 1) ∧
    IsSophieGermain (6 * x * y - 1) ∧ IsSophieGermain (6 * x * z - 1) ∧
    IsSophieGermain (6 * y * z - 1)

/-- The conjecture in OEIS A227938: `a(n) < 2n` for all `n > 2`. -/
theorem main : ∀ n : ℕ, 2 < n → Nat.nth InA227938 (n - 1) < 2 * n := by
  sorry

end OMA.S_oeis_a227938
