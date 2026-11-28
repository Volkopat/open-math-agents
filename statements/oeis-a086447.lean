import Mathlib

/-!
# A086447: least `k` such that `prime(n)` divides `prime(n+1)+⋯+prime(n+k)`.

Source: https://oeis.org/A086447
Credit: @cjchaffin

Conjecture (on the OEIS page): `a(n)` exists for every `n`. Example: `a(3) = 6` because
`prime(3) = 5` divides `7+11+13+17+19+23 = 90`.

Conventions: offset 1; `prime(n)` is the `n`-th prime with `prime(1) = 2`, written
`Nat.nth Nat.Prime (n - 1)`. The conjecture is formalized as existence of some
positive `k`, not the least-`k` part of the name.
-/

namespace OMA.S_oeis_a086447

/-- The `n`-th prime with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ, 0 < k ∧ prime n ∣ ∑ i ∈ Finset.Icc 1 k, prime (n + i) := by
  sorry

end OMA.S_oeis_a086447
