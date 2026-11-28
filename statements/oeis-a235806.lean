import Mathlib

/-!
# A235806: Odd primes p with (p^2 - 1)/4 - prime((p - 1)/2) and (p^2 - 1)/4 - prime((p + 1)/2) both prime.

Source: https://oeis.org/A235806
Credit: @gblacher2

Formalizes the OEIS comment (Zhi-Wei Sun): "By the conjecture in A235805, this sequence should
have infinitely many terms."

Conventions: `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`
in Mathlib's 0-indexed convention. For an odd prime `p`, `(p - 1) / 2 ≥ 1` and
`(p ^ 2 - 1) / 4 = k * (k + 1)` with `k = (p - 1) / 2`, so the divisions are exact. For `k ≥ 2`,
`prime(k) < prime(k + 1) ≤ k * (k + 1)`, so both natural-number subtractions are the integers of
the source. The only exception is `p = 3`, where `2 - prime(2) = -1` becomes `0`; neither value is
prime, so `3` is excluded either way, as in the source.
-/

namespace OMA.S_oeis_a235806

/-- `prime k`: the `k`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The terms of A235806: odd primes `p` such that `(p^2 - 1)/4 - prime((p - 1)/2)` and
`(p^2 - 1)/4 - prime((p + 1)/2)` are both prime. -/
def S : Set ℕ :=
  {p | p.Prime ∧ Odd p ∧ ((p ^ 2 - 1) / 4 - prime ((p - 1) / 2)).Prime ∧
    ((p ^ 2 - 1) / 4 - prime ((p + 1) / 2)).Prime}

/-- A235806 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a235806
