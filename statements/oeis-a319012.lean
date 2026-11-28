import Mathlib

/-!
# A319012: a(n) = Sum_{i=1..n} prime(n*(i - 1) + i).

Source: https://oeis.org/A319012
Credit: @sntntHb

Conjecture (stated on the OEIS page): `a(2)` and `a(3)` are the only terms that are perfect
squares (`a(2) = 9`, `a(3) = 36`).

Conventions:
- `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`.
- The offset is 1, so the terms are `a(n)` for `n ≥ 1`.
-/

namespace OMA.S_oeis_a319012

/-- `a(n) = ∑_{i=1}^{n} prime(n*(i-1) + i)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, Nat.nth Nat.Prime (n * (i - 1) + i - 1)

theorem main : {n : ℕ | 1 ≤ n ∧ IsSquare (a n)} = {2, 3} := by
  sorry

end OMA.S_oeis_a319012
