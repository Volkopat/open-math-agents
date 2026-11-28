import Mathlib

/-!
# Coefficient growth of the exponential generating expression in A276751

In Paul D. Hanna's ordinary generating function the logarithm is a sum
over r ≥ 1. A term of degree n in the r-th summand chooses an ordered
composition of n of length r. Each part k contributes k^(2r−1), and the
summand is divided by r. Exponentiating takes ordered products of these
coefficients and divides by the factorial of the outer composition length.
The empty composition gives the constant coefficient 1.

Vaclav Kotesovec conjectured in 2020 that the 1/n² power tends to the square root of two.
Source: https://oeis.org/A276751
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a276751
open Filter Topology

def weight {n : ℕ} (c : Composition n) : ℕ :=
  c.blocks.prod^(2*c.length-1)

noncomputable def logCoeff (n : ℕ) : ℝ :=
  ∑ c : Composition n, (weight c:ℝ)/(c.length:ℝ)

noncomputable def term (n : ℕ) : ℝ :=
  ∑ c : Composition n, (c.blocks.map logCoeff).prod/(c.length.factorial:ℝ)

theorem main :
    Tendsto (fun n : ℕ => (term n)^(1/(n:ℝ)^2)) atTop (𝓝 (Real.sqrt 2)) := by
  sorry

end OMA.S_oeis_a276751
