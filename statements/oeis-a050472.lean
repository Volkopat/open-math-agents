import Mathlib

/-!
# OEIS A050472: `2 φ(m) = φ(m + 1)`

Source: https://oeis.org/A050472
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A050472 lists the `m` with `2 φ(m) = φ(m + 1)`. Conjecture (OEIS entry): `a(n)/n³` is bounded.
(The entry also asks whether `a(n)/n³ → 2`.)

Conventions:
* `a(n)` is the `n`-th term (offset `1`, `Nat.nth` at `n - 1`). Boundedness presupposes that the
  sequence is infinite, which `main` includes; then `a(n) ≤ C n³` for some `C` and all `n ≥ 1`.
-/

namespace OMA.S_oeis_a050472

/-- The defining property. -/
def P (m : ℕ) : Prop := 1 ≤ m ∧ 2 * Nat.totient m = Nat.totient (m + 1)

/-- Infinitely many terms, and `a(n) = O(n³)`. -/
theorem main : {m | P m}.Infinite ∧ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → (Nat.nth P (n - 1) : ℝ) ≤ C * n ^ 3 := by
  sorry

end OMA.S_oeis_a050472
