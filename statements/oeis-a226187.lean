import Mathlib

/-!
# Ratios of the first harmonic numbers exceeding n/3 (OEIS A226187)

The n-th index is the least positive integer k whose harmonic sum H_k is
strictly greater than n/3. The OEIS entry conjectures a limiting ratio
1.39..., and Ralf Stephan identifies the proposed exact value as exp(1/3).

Source: https://oeis.org/A226187
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a226187
open Filter Topology

noncomputable def firstAbove (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ (n:ℝ)/3 < (harmonic k:ℝ)}

theorem main :
    Tendsto (fun n : ℕ => (firstAbove (n+1):ℝ)/(firstAbove n:ℝ)) atTop
      (𝓝 (Real.exp (1/3))) := by
  sorry

end OMA.S_oeis_a226187
