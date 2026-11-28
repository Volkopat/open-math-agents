import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Rat.Lemmas

/-!
Source: https://oeis.org/A166272, conjecture of Antti Karttunen.
Related definitions: https://oeis.org/A166100, https://oeis.org/A166101,
and https://oeis.org/A166102. OEIS Foundation, CC BY-SA 4.0.
-/

namespace OMA.S_oeis_a166272

open Finset

def positiveResidues (m : ℕ) : Finset ℕ :=
  (Icc 1 m).filter fun x => jacobiSym (x : ℤ) m = 1

def jacobiSum (m : ℕ) : ℕ := ∑ x ∈ positiveResidues m, x

/-- At index k, A166100 sums through 2k+1 inclusive. The associated odd modulus is 2k+1. -/
def quotient (k : ℕ) : ℚ :=
  (jacobiSum (2 * k + 1) : ℚ) / ((2 * k + 1 : ℕ) : ℚ)

/-- A166101 enumerates exactly the indices k for which this quotient is nonintegral.
A166102 gives their corresponding moduli. A166272 conjectures that each reduced
denominator in this enumeration is 3. -/
theorem main : ∀ k : ℕ, (quotient k).den ≠ 1 → (quotient k).den = 3 := by
  sorry

end OMA.S_oeis_a166272
