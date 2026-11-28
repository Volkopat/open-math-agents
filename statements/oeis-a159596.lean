import Mathlib

/-!
# Iterated Euler derivatives in OEIS A159596

The ordinary generating function in A159596 is exp(Σ_{r≥1} (D^r B(x))^r/r),
where B(x)=x/(1-x)^2 and D=x*d/dx. The coefficient of x^k in D^r B is
k^(r+1). In the r-fold product, the ordered positive degrees form a
composition of n of length r. Multiplying their contributions gives the
product of the degrees raised to r+1. The outer factorial-weighted sum
expands the exponential. Vaclav Kotesovec conjectured the limit in 2023.
Source: https://oeis.org/A159596
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a159596
open Filter Topology

def weight {n : ℕ} (c : Composition n) : ℕ := c.blocks.prod^(c.length+1)

noncomputable def logCoeff (n : ℕ) : ℝ :=
  ∑ c : Composition n, (weight c:ℝ)/(c.length:ℝ)

noncomputable def term (n : ℕ) : ℝ :=
  ∑ c : Composition n, (c.blocks.map logCoeff).prod/(c.length.factorial:ℝ)

theorem main :
    Tendsto (fun n : ℕ => (term n)^(1/(n:ℝ)^2)) atTop (𝓝 ((2:ℝ)^((1:ℝ)/4))) := by
  sorry

end OMA.S_oeis_a159596
