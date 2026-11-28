import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Kotesovec's logarithmic conjecture for OEIS A292414

Source: https://oeis.org/A292414 (Vaclav Kotesovec, August 22, 2018).
Credit: @NOELOO6

For each n the product has the fixed weight 2^n in every factor. Its degree-n
coefficient defines a(n). The power series topology is coefficientwise. The
conclusion is asymptotic equivalence with the natural logarithm.
-/

namespace OMA.S_oeis_a292414
open PowerSeries Filter
open scoped PowerSeries PowerSeries.WithPiTopology Asymptotics

noncomputable def a (n : ℕ) : ℕ :=
  coeff n (∏' k : ℕ, (1+C (2^n:ℕ)*X^(k+1) : ℕ⟦X⟧))

theorem main :
    (fun n : ℕ => Real.log (a n)) ~[atTop]
      (fun n : ℕ => Real.sqrt 2 * Real.log 2 * (n:ℝ)^(3/2:ℝ)) := by
  sorry

end OMA.S_oeis_a292414
