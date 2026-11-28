import Mathlib

/-!
# A072849: indices `n` for which `prime(n)+⋯+prime(n+3)` is a square.

Source: https://oeis.org/A072849 (and A064397)
Credit: @cjchaffin

Conjecture (Jianing Song, Nov 13 2022): this sequence and A064397 (indices `n` for which
`prime(n)+prime(n+1)` is a square) are disjoint. Equivalently, as stated on the page,
`prime(n)+prime(n+1)` and `prime(n)+⋯+prime(n+3)` cannot be squares at the same time.

Conventions: `prime(n)` is the `n`-th prime with `prime(1) = 2`, written
`Nat.nth Nat.Prime (n - 1)`; the quantified `n` starts at 1.
-/

namespace OMA.S_oeis_a072849

/-- The `n`-th prime with `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

theorem main : ∀ n : ℕ, 1 ≤ n →
    ¬ (IsSquare (prime n + prime (n + 1)) ∧
        IsSquare (prime n + prime (n + 1) + prime (n + 2) + prime (n + 3))) := by
  sorry

end OMA.S_oeis_a072849
