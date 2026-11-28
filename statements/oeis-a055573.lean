import Mathlib

/-!
# OEIS A055573: continued fraction length of harmonic numbers

Source: https://oeis.org/A055573
`a n` is the number of terms in the simple continued fraction of the harmonic number
`H_n = ∑_{k=1}^{n} 1/k`. Conjecture (Cloitre): `a(n)/n → 12 log 2 / π²` (Lévy's constant
A089729).

Conventions. The continued fraction is Mathlib's `GenContFract.of` over `ℚ`, which terminates
for rationals; the number of terms is `1` (integer part) plus the number of partial
denominators, the latter being the first index at which `partDens` is exhausted.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a055573

open Filter Topology Real

/-- The harmonic number `H_n`. -/
def H (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℚ)

/-- Number of terms of the simple continued fraction of `H_n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  1 + sInf {k | (GenContFract.of (H n)).partDens.get? k = none}

theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (12 * log 2 / π ^ 2)) := by
  sorry

end OMA.S_oeis_a055573
