import Mathlib

/-!
# OEIS A083552: lcm/gcd of consecutive prime gaps

Source: https://oeis.org/A083552
`a n = lcm(d(n), d(n+1)) / gcd(d(n), d(n+1))` where `d(n) = prime(n+1) - prime(n)`.
Conjecture (Borysowicz, 2018): every positive integer appears infinitely many times.

Conventions. `prime(n) = Nat.nth Nat.Prime (n - 1)`, `n ≥ 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a083552

/-- `d(n) = prime(n+1) - prime(n)`. -/
noncomputable def d (n : ℕ) : ℕ := Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

/-- A083552. -/
noncomputable def a (n : ℕ) : ℕ := Nat.lcm (d n) (d (n + 1)) / Nat.gcd (d n) (d (n + 1))

theorem main : ∀ m : ℕ, 1 ≤ m → {n : ℕ | 1 ≤ n ∧ a n = m}.Infinite := by
  sorry

end OMA.S_oeis_a083552
