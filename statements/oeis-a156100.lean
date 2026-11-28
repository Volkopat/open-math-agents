import Mathlib

/-!
# The exponential generating expression of A156100

Paul D. Hanna gives the ordinary generating function
A(x) = exp(Σ_{r≥1} x^r (1+2^r x)^r/r).
In its logarithm, each of the r factors is x+2^r x^2. Each ordered part
therefore has degree one with weight one, or degree two with weight 2^r.
Taking ordered compositions of the total degree implements the product.
The outer composition sum, with a factorial denominator, implements exp.
Vaclav Kotesovec conjectured the fourth-root growth rate in 2020.
Source: https://oeis.org/A156100
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a156100
open Filter Topology

def partWeight (k : ℕ) : ℕ := if k=1 then 1 else if k=2 then 2 else 0

def weight {n : ℕ} (c : Composition n) : ℕ := (c.blocks.map partWeight).prod^c.length

noncomputable def logCoeff (n : ℕ) : ℝ :=
  ∑ c : Composition n, (weight c:ℝ)/(c.length:ℝ)

noncomputable def term (n : ℕ) : ℝ :=
  ∑ c : Composition n, (c.blocks.map logCoeff).prod/(c.length.factorial:ℝ)

theorem main :
    Tendsto (fun n : ℕ => (term n)^(1/(n:ℝ)^2)) atTop (𝓝 ((2:ℝ)^((1:ℝ)/4))) := by
  sorry

end OMA.S_oeis_a156100
