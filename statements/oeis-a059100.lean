import Mathlib

/-!
# OEIS A059100: largest partial quotient of ∑ 1/n^(2^k)

Source: https://oeis.org/A059100 (`a n = n² + 2`)
Conjecture on the entry: let `s(n) = ∑_{k ≥ 1} 1/n^(2^k)`. Then the maximum element in the
continued fraction of `s(n)` is `n² + 2`.

Conventions. `n ≥ 2` (for `n = 1` the series diverges). The elements of the continued fraction
are its integer part and partial denominators, as produced by Mathlib's `GenContFract.of`;
the integer part of `s(n)` is `0`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a059100

/-- `s(n) = ∑_{k ≥ 1} 1/n^(2^k)`. -/
noncomputable def s (n : ℕ) : ℝ := ∑' k : ℕ, 1 / (n : ℝ) ^ (2 ^ (k + 1))

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      IsGreatest {b : ℝ | ∃ i, (GenContFract.of (s n)).partDens.get? i = some b}
        ((n : ℝ) ^ 2 + 2) := by
  sorry

end OMA.S_oeis_a059100
