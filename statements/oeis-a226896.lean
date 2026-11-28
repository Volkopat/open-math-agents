import Mathlib

/-!
# The reciprocal harmonic-number error in OEIS A226896

Clark Kimberling's 2013 comment conjectures that the reciprocal of
H_n − γ − log(n), less 2n, tends to 1/3. Here harmonic is the rational
harmonic number in Mathlib and Real.eulerMascheroniConstant is γ.
The sequence is evaluated along natural n tending to infinity.
Source: https://oeis.org/A226896
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a226896
open Filter Topology

theorem main :
    Tendsto (fun n : ℕ => 1/((harmonic n:ℝ) - Real.eulerMascheroniConstant - Real.log n) - 2*n)
      atTop (𝓝 ((1:ℝ)/3)) := by
  sorry

end OMA.S_oeis_a226896
