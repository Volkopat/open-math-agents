import Mathlib

/-!
# A208548: a(n) = floor((4/3)*(2+prime(n)) - prime(n+1)).

Source: https://oeis.org/A208548
Credit: @eltociear

`prime(n)` is the `n`-th prime (`prime(1) = 2`), which is `Nat.nth Nat.Prime (n - 1)` since
`Nat.nth` counts from `0`. `a(n)` (offset 1) is `floor((4/3) * (2 + prime(n)) - prime(n+1))`
(`a(1) = 2`, `a(2) = 1`, `a(3) = 2`). The entry conjectures:

  a(n) > 0 for all n.

`main` states this for every `n ≥ 1`. The expression is evaluated in `ℚ` and the floor is
`Int.floor`.
-/

namespace OMA.S_oeis_a208548

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- OEIS A208548: `⌊(4/3) * (2 + prime(n)) - prime(n+1)⌋`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊(4 / 3 : ℚ) * (2 + (prime n : ℚ)) - (prime (n + 1) : ℚ)⌋

/-- The conjecture in OEIS A208548: `a(n) > 0` for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a208548
-- ci: re-run check-proof
