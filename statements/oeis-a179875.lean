import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Equal antiharmonic means of consecutive reduced residue systems

Amiram Eldar conjectured in OEIS A179875 that these equalities occur exactly
at the consecutive Möbius values 1 and −1. Take the representatives from 1
through n. For n > 1 these are all strictly below n. For n = 1 this gives
the singleton {1} and the initial mean B(1) = 1 recorded in A175505/A175506.

Sources: https://oeis.org/A179875, https://oeis.org/A175505, https://oeis.org/A175506.
-/

namespace OMA.S_oeis_a179875

def residues (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun k => k.Coprime n)

/-- The antiharmonic mean is the sum of the squares divided by the sum. -/
def mean (n : ℕ) : ℚ :=
  (∑ k ∈ residues n, (k : ℚ)^2) / (∑ k ∈ residues n, (k : ℚ))

theorem main : ∀ k : ℕ, 0 < k →
    (mean k = mean (k+1) ↔
      ArithmeticFunction.moebius k = 1 ∧ ArithmeticFunction.moebius (k+1) = -1) := by
  sorry

end OMA.S_oeis_a179875
