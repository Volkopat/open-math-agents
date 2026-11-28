import Mathlib

/-!
# A207480: a(n) = (3/2)*(1+prime(n)) - prime(n+1).

Source: https://oeis.org/A207480
Credit: @eltociear

`prime(n)` is the `n`-th prime (`prime(1) = 2`), which is `Nat.nth Nat.Prime (n - 1)` since
`Nat.nth` counts from `0`. The entry has offset 2 (because `a(1) = 3/2` is not an integer) and
conjectures:

  a(n) > 0 for all n,

i.e. `(3/2) * (1 + prime(n)) - prime(n+1) > 0`. `main` states this over the sequence's range
`n ≥ 2`, computing in `ℚ` so that the factor `3/2` is exact.
-/

namespace OMA.S_oeis_a207480

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- OEIS A207480: `(3/2) * (1 + prime(n)) - prime(n+1)`, as a rational number. -/
noncomputable def a (n : ℕ) : ℚ := (3 / 2 : ℚ) * (1 + (prime n : ℚ)) - (prime (n + 1) : ℚ)

/-- The conjecture in OEIS A207480: `a(n) > 0` for all `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a207480
-- ci: re-run check-proof
