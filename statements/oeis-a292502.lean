import Mathlib

/-!
# The coefficient growth of Hanna's logarithmic generating function (A292502)

The entry defines a(n) as n times the coefficient of x^n in the sum over
r ≥ 1 of (sum over k ≥ 1 of (2k-1)^r x^k)^r/r. Coefficient extraction
picks an ordered list of r positive block sizes with total n. Its weight
is the r-th power of the product of their odd numbers, divided by r.
Multiplying by n gives the finite composition sum below for every n ≥ 1.
The growth conjecture is due to Vaclav Kotesovec (2020).

Source: https://oeis.org/A292502
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a292502
open Filter Topology

def oddProduct (blocks : List ℕ) : ℕ := (blocks.map (fun k => 2*k-1)).prod

noncomputable def term (n : ℕ) : ℝ :=
  ∑ c : Composition n, (n:ℝ)/(c.length:ℝ)*(oddProduct c.blocks:ℝ)^c.length

theorem main :
    Tendsto (fun n : ℕ => (term n)^(1/(n:ℝ)^2)) atTop (𝓝 ((3:ℝ)^((1:ℝ)/4))) := by
  sorry

end OMA.S_oeis_a292502
