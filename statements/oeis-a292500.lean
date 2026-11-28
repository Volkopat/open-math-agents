import Mathlib

/-!
# Coefficient growth of the exponential generating expression in A292500

In Paul D. Hanna's ordinary generating function the logarithm is a sum
over r ≥ 1. A term of degree n in the r-th summand chooses an ordered
composition of n of length r. Each part k contributes (2k−1)^r, and the
summand is divided by r. Exponentiating takes ordered products of these
coefficients and divides by the factorial of the outer composition length.
The empty composition gives the constant coefficient 1.

Vaclav Kotesovec conjectured in 2020 that the 1/n² power tends to the fourth root of three.
Source: https://oeis.org/A292500
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a292500
open Filter Topology

def weight {n : ℕ} (c : Composition n) : ℕ :=
  (c.blocks.map (fun k => 2*k-1)).prod^c.length

noncomputable def logCoeff (n : ℕ) : ℝ :=
  ∑ c : Composition n, (weight c:ℝ)/(c.length:ℝ)

noncomputable def term (n : ℕ) : ℝ :=
  ∑ c : Composition n, (c.blocks.map logCoeff).prod/(c.length.factorial:ℝ)

theorem main :
    Tendsto (fun n : ℕ => (term n)^(1/(n:ℝ)^2)) atTop (𝓝 ((3:ℝ)^((1:ℝ)/4))) := by
  sorry

end OMA.S_oeis_a292500
