import Mathlib

/-!
# OEIS A338274: Goldbach decompositions with a bounded half-gap

Source: https://oeis.org/A338274
Credit: @yuka30240

Ya-Ping Lu's two conjectures use the midpoint of the prime pair,
denoted by both `n` and `m` in the source. We use `n` throughout.
-/

namespace OMA.S_oeis_a338274

/-- Count each unordered pair once by its nonnegative half-gap `d`.
The strict square bound excludes equality even when `2 * n - 1` is a square. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range ((2 * n - 1).sqrt + 1)).filter fun d =>
    d ^ 2 < 2 * n - 1 ∧ (n - d).Prime ∧ (n + d).Prime).card

/-- Beyond the last listed zero, every midpoint admits a pair. Every new
record count of at least two occurs at a midpoint divisible by five. -/
theorem main :
    (∀ n : ℕ, 1353559 < n → 0 < a n) ∧
    (∀ n : ℕ, 2 ≤ n → 2 ≤ a n → (∀ k : ℕ, 2 ≤ k → k < n → a k < a n) → 5 ∣ n) := by
  sorry

end OMA.S_oeis_a338274

