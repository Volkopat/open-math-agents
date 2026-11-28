import Mathlib

/-!
# OEIS A065255: numbers ending in the same digit as their divisor sum

Source: https://oeis.org/A065255
Let `b(k)` be the `k`-th positive integer `m` such that `m` and `σ(m)` end with the same decimal
digit. Conjecture: `b(k)/k → 10`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a065255

open Filter Topology

/-- `m ≥ 1` and `σ(m) ≡ m (mod 10)`. -/
def P (m : ℕ) : Prop := 1 ≤ m ∧ (∑ d ∈ m.divisors, d) % 10 = m % 10

/-- `b k`, indexed from `1`. -/
noncomputable def b (k : ℕ) : ℕ := Nat.nth P (k - 1)

theorem main : Tendsto (fun k : ℕ => (b k : ℝ) / k) atTop (𝓝 10) := by
  sorry

end OMA.S_oeis_a065255
