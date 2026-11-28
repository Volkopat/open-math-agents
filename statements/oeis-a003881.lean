import Mathlib

/-!
# A003881: Decimal expansion of Pi/4.

Source: https://oeis.org/A003881
Credit: @<your GitHub handle>

The entry records the conjecture (Mats Granvik, Feb 23 2011)

  Pi/4 = lim_{n->oo} n*A001586(n-1)/A001586(n),

where A001586 (https://oeis.org/A001586) are the Springer numbers (generalized Euler numbers)
`1, 1, 3, 11, 57, 361, 2763, ...` with offset 0, defined there by the exponential generating
function `1/(cos(x) - sin(x))`.

We define `springer n` as `n!` times the `n`-th coefficient of the formal power series
`(cos X - sin X)⁻¹` over `ℚ` (its constant coefficient is `1`, so the inverse is the genuine
multiplicative inverse). `main` states that the real sequence `n * springer (n-1) / springer n`
tends to `π / 4`. (For `n = 0` the term is `0`, which does not affect the limit.)
-/

namespace OMA.S_oeis_a003881

open PowerSeries Filter Topology

/-- The Springer numbers (OEIS A001586): `n!` times the `n`-th coefficient of the e.g.f.
`1 / (cos x - sin x)`. -/
noncomputable def springer (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * coeff n ((cos ℚ - sin ℚ)⁻¹)

/-- Granvik's conjecture in OEIS A003881: `lim_{n→∞} n * A001586(n-1) / A001586(n) = π / 4`. -/
theorem main :
    Tendsto (fun n : ℕ => (n : ℝ) * (springer (n - 1) : ℝ) / (springer n : ℝ)) atTop
      (𝓝 (Real.pi / 4)) := by
  sorry

end OMA.S_oeis_a003881
