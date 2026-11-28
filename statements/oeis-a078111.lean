import Mathlib

/-!
# A078111: Greathouse's asymptotic for the expression inside the floor

Source: https://oeis.org/A078111

Charles R. Greathouse IV conjectured that `(n+2)^(n+2)/n^n` is
`exp(2) * (n^2 + 2*n + 2/3 + o(1))` as `n` tends to infinity.
Sela Fried proved quantitative bounds implying this asymptotic in
Theorem 17 of https://arxiv.org/abs/2607.24832.

The offset-zero convention uses the real powers with natural exponents,
so `0^0 = 1`. The value at zero has no effect on the limit.
-/

open Filter Topology

namespace OMA.S_oeis_a078111

/-- The real expression whose floor defines the sequence. -/
noncomputable def quotient (n : ℕ) : ℝ :=
  ((n : ℝ) + 2) ^ (n + 2) / (n : ℝ) ^ n

/-- Greathouse's conjectured asymptotic for the expression defining A078111. -/
theorem main : Tendsto
    (fun n : ℕ => quotient n / Real.exp 2 - ((n : ℝ)^2 + 2*n + 2/3))
    atTop (𝓝 0) := by
  sorry

end OMA.S_oeis_a078111
