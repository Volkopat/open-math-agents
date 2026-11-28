import Mathlib

/-!
# A352743: Product_{k=1..n} (p(k+1) + p(k))/(p(k+1) - p(k)) is an integer

Source: https://oeis.org/A352743

A352743 (offset 0): `a(n) = Product_{k=1..n} (p(k+1) + p(k))/(p(k+1) - p(k))`, where
`p(k) = prime(k)`: 1, 5, 20, 120, 540, 6480, 48600, 874800, …  For example
`a(4) = ((3+2)/(3-2))*((5+3)/(5-3))*((7+5)/(7-5))*((11+7)/(11-7)) = 540`.

Conjecture (Thomas Ordowski, Apr 01 2022): `a(n)` is an integer for every natural `n`. The
entry notes that this has been checked up to `n = 10^6` (Michael S. Branicky).

Conventions:
- `p(k)` is the `k`-th prime with `p(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`.
- The product is formed in `ℚ` with exact rational division (the denominators `p(k+1) - p(k)`
  are positive), over `k` in `Finset.Icc 1 n`; for `n = 0` it is the empty product `1`.
- `a(n)` is an integer when it equals the cast of some `z : ℤ`.
-/

namespace OMA.S_oeis_a352743

/-- The `k`-th prime, with `p 1 = 2`. -/
noncomputable def p (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A352743 as a rational number: `Product_{k=1..n} (p(k+1) + p(k))/(p(k+1) - p(k))`. -/
noncomputable def a (n : ℕ) : ℚ :=
  ∏ k ∈ Finset.Icc 1 n, ((p (k + 1) : ℚ) + (p k : ℚ)) / ((p (k + 1) : ℚ) - (p k : ℚ))

theorem main : ∀ n : ℕ, ∃ z : ℤ, a n = (z : ℚ) := by
  sorry

end OMA.S_oeis_a352743
