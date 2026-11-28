import Mathlib

/-!
# Fourth-root growth for the exponential series with the factor (1-x)^r

Paul D. Hanna's entry A292501 defines an ordinary generating function.
In the logarithm, the r-th summand is the r-th power of
(1-x) times the series with coefficients (2k-1)^r, divided by r.
For k ≥ 1 its individual part coefficient is the difference between
two successive odd powers; the preceding coefficient at k=1 is zero.
An ordered composition extracts the coefficient of the r-th power.
A second ordered composition with factorial denominator exponentiates
the logarithm. The empty product supplies the constant term.

Vaclav Kotesovec's 2020 conjecture concerns the 1/n² power of a(n).
Source: https://oeis.org/A292501
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a292501
open Filter Topology

def partWeight (r k : ℕ) : ℕ := (2*k-1)^r - (2*k-3)^r

def weight {n : ℕ} (c : Composition n) : ℕ :=
  (c.blocks.map (partWeight c.length)).prod

noncomputable def logCoeff (n : ℕ) : ℝ :=
  ∑ c : Composition n, (weight c:ℝ)/(c.length:ℝ)

noncomputable def term (n : ℕ) : ℝ :=
  ∑ c : Composition n, (c.blocks.map logCoeff).prod/(c.length.factorial:ℝ)

theorem main :
    Tendsto (fun n : ℕ => (term n)^(1/(n:ℝ)^2)) atTop (𝓝 ((3:ℝ)^((1:ℝ)/4))) := by
  sorry

end OMA.S_oeis_a292501
