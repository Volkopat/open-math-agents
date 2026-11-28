import Mathlib

/-!
# OEIS A083414

Arrange 1 through `n ^ 2` in `n` rows of length `n`. The conjecture says
that the minimum prime count among columns coprime to `n` is positive
whenever `n > 1`. Equivalently, each such column contains a prime.
Column `k` has entries `i * n + k` for `0 ≤ i < n`.

Source: https://oeis.org/A083414
Formalization: @a5teri5k
-/

namespace OMA.S_oeis_a083414

theorem main : ∀ n : ℕ, 1 < n → ∀ k : ℕ, 1 ≤ k → k ≤ n → Nat.Coprime k n →
    ∃ i : ℕ, i < n ∧ Nat.Prime (i * n + k) := by
  sorry

end OMA.S_oeis_a083414
