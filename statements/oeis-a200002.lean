import Mathlib

/-!
# Central binomial coefficients in the logarithm of A200002

Paul D. Hanna defines the ordinary generating function
A(x) = exp(Σ_{r≥1} binom(2r,r)^r x^r/(2^r r)).
Here logCoeff is the coefficient of its logarithm. The zero denominator
at r = 0 gives the desired zero constant in Lean. The coefficient in the
exponential is the finite sum over ordered compositions, divided by the
factorial of the number of factors. The empty composition gives a(0)=1.
Vaclav Kotesovec conjectured the growth limit 4 in 2014.
Source: https://oeis.org/A200002
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a200002
open Filter Topology

noncomputable def logCoeff (n : ℕ) : ℝ :=
  (n.centralBinom:ℝ)^n / ((2:ℝ)^n * (n:ℝ))

noncomputable def term (n : ℕ) : ℝ :=
  ∑ c : Composition n, (c.blocks.map logCoeff).prod / (c.length.factorial:ℝ)

theorem main :
    Tendsto (fun n : ℕ => (term n)^(1/(n:ℝ)^2)) atTop (𝓝 4) := by
  sorry

end OMA.S_oeis_a200002
