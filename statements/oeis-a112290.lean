import Mathlib

/-!
# The limit of the reciprocal Stirling row sums (OEIS A112290)

A112290 and A112291 are the numerator and denominator in lowest terms of
the sum of the reciprocals of S(n,k), for k from 1 to n inclusive. Here
S denotes the Stirling numbers of the second kind. Vaclav Kotesovec
conjectured in 2022 that the quotient tends to two.

Sources: https://oeis.org/A112290 and https://oeis.org/A112291
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a112290
open Filter Topology

def reciprocalSum (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (Nat.stirlingSecond n (i+1) : ℚ)⁻¹

def numerator (n : ℕ) : ℤ := (reciprocalSum n).num
def denominator (n : ℕ) : ℕ := (reciprocalSum n).den

theorem main :
    Tendsto (fun n : ℕ => (numerator n : ℝ)/(denominator n : ℝ)) atTop (𝓝 2) := by
  sorry

end OMA.S_oeis_a112290
