import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Floor.Defs

/-! Source: https://mathoverflow.net/questions/433154 -/

namespace OMA.S_mo_433154

noncomputable def decimalDigit (x : ℝ) (n : ℕ) : ℕ :=
  ⌊x * 10 ^ (n + 1)⌋₊ % 10

noncomputable def interleave (x y : ℝ) : ℝ :=
  ∑' n : ℕ,
    ((decimalDigit x n : ℝ) / 10 ^ (2 * n + 1) +
      (decimalDigit y n : ℝ) / 10 ^ (2 * n + 2))

theorem main :
    ∀ x y : ℝ, 0 ≤ x → x < 1 → 0 ≤ y → y < 1 →
      Transcendental ℚ x → Transcendental ℚ y →
      Transcendental ℚ (interleave x y) := by
  sorry

end OMA.S_mo_433154
