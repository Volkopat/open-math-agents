import Mathlib.Data.Nat.Digits.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A346695: Density of numbers with more divisors than binary digits

Source: https://oeis.org/A346695
Credit: @Alienchisel

The sequence contains positive integers whose number of positive divisors
exceeds the length of their binary expansion. The conjecture says that
the proportion of such integers among 1 through x tends to zero.
-/

namespace OMA.S_oeis_a346695

open Filter
open scoped Topology

/-- The positive integers at most the cutoff that satisfy the OEIS digit test. -/
def qualifyingUpTo (cutoff : ℕ) : Finset ℕ :=
  (Finset.Icc 1 cutoff).filter fun n => (Nat.digits 2 n).length < n.divisors.card

theorem main :
    Tendsto (fun x : ℕ => ((qualifyingUpTo x).card : ℝ) / (x : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  sorry

end OMA.S_oeis_a346695
