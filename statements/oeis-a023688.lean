import Mathlib

/-!
# OEIS A023688: 2-adic valuations of A005148 and binary weight

Source: https://oeis.org/A023688
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A023688 lists the numbers with exactly `6` ones in binary. General conjecture (OEIS entry): the
numbers `k` such that `8^j` is the highest power of `2` dividing `A005148(k)` are exactly the
numbers with `j + 1` ones in binary; here `A005148(k) = (1/24) [x^k] ∏_{m ≥ 1} (1 + x^(2m-1))^(24k)`.

Conventions:
* `k ≥ 1` (`A005148(0) = 0`). The coefficient of `x^k` only involves the factors with
  `2m - 1 ≤ k`, so the product is truncated at `m ≤ k`. The conjecture for all `j` at once says
  `v₂(A005148(k)) = 3 (s₂(k) - 1)`, `s₂` the binary weight.
-/

namespace OMA.S_oeis_a023688

open Polynomial

/-- `24 · A005148(k)`: the coefficient of `x^k` in `∏ (1 + x^(2m-1))^(24k)`. -/
noncomputable def c (k : ℕ) : ℤ :=
  (∏ m ∈ Finset.range k, (1 + X ^ (2 * m + 1) : ℤ[X]) ^ (24 * k)).coeff k

/-- A005148. -/
noncomputable def A005148 (k : ℕ) : ℤ := c k / 24

/-- Binary weight. -/
def s2 (k : ℕ) : ℕ := ((Nat.digits 2 k).filter (· = 1)).length

/-- `v₂(A005148(k)) = 3(s₂(k) - 1)` for `k ≥ 1`. -/
theorem main : ∀ k : ℕ, 1 ≤ k → padicValInt 2 (A005148 k) = 3 * (s2 k - 1) := by
  sorry

end OMA.S_oeis_a023688
