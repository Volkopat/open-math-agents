import Mathlib

/-!
# OEIS A011754: binary weight of powers of 3

Source: https://oeis.org/A011754
`a n` is the number of `1`s in the binary expansion of `3^n`. Conjecture (Ed Pegg):
`a n / n → log 3 / (2 log 2)`, i.e. about half of the bits of `3^n` are `1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a011754

open Filter Topology Real

/-- Number of ones in the binary expansion of `3^n`. -/
def a (n : ℕ) : ℕ := ((Nat.digits 2 (3 ^ n)).filter (· = 1)).length

theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (log 3 / (2 * log 2))) := by
  sorry

end OMA.S_oeis_a011754
