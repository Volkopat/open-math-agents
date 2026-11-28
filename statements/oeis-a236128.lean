import Mathlib

/-!
# A236128: Iterated prime factors of Mersenne numbers

Source: https://oeis.org/A236128
Formalization: @pyaf

The greatest and least prime factors are taken separately in the two conjectures.
-/

namespace OMA.S_oeis_a236128

def gpf (m : ℕ) : ℕ := m.primeFactors.sup id

theorem main : {p : ℕ | p.Prime ∧ gpf (gpf (2 ^ p - 1) - 1) = p}.Finite ∧
    {p : ℕ | p.Prime ∧ gpf ((2 ^ p - 1).minFac - 1) = p}.Infinite := by
  sorry

end OMA.S_oeis_a236128
