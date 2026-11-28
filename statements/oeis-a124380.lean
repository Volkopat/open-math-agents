import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Kotesovec's asymptotic for the coefficients of OEIS A124380

Source: https://oeis.org/A124380 (Vaclav Kotesovec, September 18, 2024).
Credit: @NOELOO6

The original ordinary generating function is the sum over j≥0 of X^j times
the product of 1+kX for k from 0 through j. The conclusion uses asymptotic
equivalence of real functions with the natural logarithm.
-/

namespace OMA.S_oeis_a124380
open PowerSeries Filter Finset
open scoped PowerSeries PowerSeries.WithPiTopology Asymptotics

noncomputable def S : ℕ⟦X⟧ :=
  ∑' j : ℕ, X^j * ∏ k ∈ range (j+1), (1+C k*X : ℕ⟦X⟧)

theorem main : (fun n : ℕ => Real.log ((coeff n S : ℕ):ℝ)) ~[atTop]
    (fun n : ℕ => (n:ℝ)*Real.log n/2-n*(1+Real.log 2)/2) := by
  sorry

end OMA.S_oeis_a124380
