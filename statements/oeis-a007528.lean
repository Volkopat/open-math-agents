import Mathlib

/-!
# OEIS A007528: a product over primes `6k ± 1`

Source: https://oeis.org/A007528
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A007528 lists the primes `≡ 5 (mod 6)` and A002476 the primes `≡ 1 (mod 6)`. Conjecture (OEIS
entry): `∏_{n ≥ 1} ((a(n) - 1)/(a(n) + 1)) · ((b(n) + 1)/(b(n) - 1)) = 3/4` with `a = A007528`,
`b = A002476`.

Conventions:
* `a n` and `b n` are the `n`-th primes (from `0`) in the two residue classes (`Nat.nth`). The
  infinite product is the limit of its partial products over `n < N`, `N → ∞`.
-/

namespace OMA.S_oeis_a007528

open Filter Topology

/-- The `n`-th prime `≡ 5 (mod 6)`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun p => p.Prime ∧ p % 6 = 5) n

/-- The `n`-th prime `≡ 1 (mod 6)`. -/
noncomputable def b (n : ℕ) : ℕ := Nat.nth (fun p => p.Prime ∧ p % 6 = 1) n

/-- The partial products converge to `3/4`. -/
theorem main : Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N,
    (((a n : ℝ) - 1) / ((a n : ℝ) + 1)) * (((b n : ℝ) + 1) / ((b n : ℝ) - 1))) atTop (𝓝 (3 / 4)) := by
  sorry

end OMA.S_oeis_a007528
