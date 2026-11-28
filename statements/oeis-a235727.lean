import Mathlib

/-!
# A235727: Odd primes p with (p^2 - 1)/4 - prime((p - 1)/2) and (p^2 - 1)/4 + prime((p - 1)/2) both prime.

Source: https://oeis.org/A235727
Credit: @gblacher2

Formalizes the OEIS comment (Zhi-Wei Sun): "By the conjecture in A235728, this sequence should
have infinitely many terms."

Conventions: `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`
in Mathlib's 0-indexed convention. For an odd prime `p`, `(p - 1) / 2 ≥ 1` and
`(p ^ 2 - 1) / 4 = k * (k + 1)` with `k = (p - 1) / 2`, so the divisions are exact. Since
`prime(k) ≤ k * (k + 1)` for every `k ≥ 1`, the natural-number subtraction
`(p ^ 2 - 1) / 4 - prime((p - 1) / 2)` is the integer of the source (for `p = 3` it is `0`).
-/

namespace OMA.S_oeis_a235727

/-- `prime k`: the `k`-th prime, 1-indexed, so `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The terms of A235727: odd primes `p` such that `(p^2 - 1)/4 - prime((p - 1)/2)` and
`(p^2 - 1)/4 + prime((p - 1)/2)` are both prime. -/
def S : Set ℕ :=
  {p | p.Prime ∧ Odd p ∧ ((p ^ 2 - 1) / 4 - prime ((p - 1) / 2)).Prime ∧
    ((p ^ 2 - 1) / 4 + prime ((p - 1) / 2)).Prime}

/-- A235727 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a235727
