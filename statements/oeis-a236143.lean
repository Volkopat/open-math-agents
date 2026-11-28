import Mathlib

/-!
# A236143: Odd primes p with prime(p-1) - (p-1) and prime(p-1) - 2*prime((p-1)/2) both prime.

Source: https://oeis.org/A236143
Credit: @gblacher2

Formalizes the OEIS comment (Zhi-Wei Sun): "By part (i) of the conjecture in A236138, this
sequence should have infinitely many terms."

Conventions: `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`
in Mathlib's 0-indexed convention. For an odd prime `p`, `p - 1 ≥ 2` and `(p - 1) / 2 ≥ 1`, so
`prime` is only evaluated at positive indices and the division is exact. Natural-number
subtraction truncates a negative value to `0`; since neither a negative integer nor `0` is prime,
each primality condition holds for the truncated value exactly when it holds for the integer of
the source (this only matters for `p = 3`, where `prime(2) - 2 * prime(1) = -1`).
-/

namespace OMA.S_oeis_a236143

/-- `prime k`: the `k`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The terms of A236143: odd primes `p` such that `prime(p - 1) - (p - 1)` and
`prime(p - 1) - 2 * prime((p - 1) / 2)` are both prime. -/
def S : Set ℕ :=
  {p | p.Prime ∧ Odd p ∧ (prime (p - 1) - (p - 1)).Prime ∧
    (prime (p - 1) - 2 * prime ((p - 1) / 2)).Prime}

/-- A236143 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a236143
