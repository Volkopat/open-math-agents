import Mathlib

/-!
# OEIS A091590: continued fraction length of H_(10^n)

Source: https://oeis.org/A091590
`a n` is the number of terms in the simple continued fraction of the harmonic number `H_(10^n)`.
Conjecture (Cloitre, 2002): `a(n) / 10^n → 12 log 2 / π²`.

Conventions. The continued fraction is Mathlib's `GenContFract.of` over `ℚ`; the number of
terms is `1` (integer part) plus the number of partial denominators.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a091590

open Filter Topology Real

/-- The harmonic number `H_m`. -/
def H (m : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 m, 1 / (k : ℚ)

/-- Number of terms of the simple continued fraction of `H_(10^n)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  1 + sInf {k | (GenContFract.of (H (10 ^ n))).partDens.get? k = none}

theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / 10 ^ n) atTop (𝓝 (12 * log 2 / π ^ 2)) := by
  sorry

end OMA.S_oeis_a091590
