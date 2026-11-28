import Mathlib

/-!
# A114887: Multiperfect numbers sigma(n) = k*n, which are divisible by the sum of their prime factors without repetition.

Source: https://oeis.org/A114887
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

open scoped ArithmeticFunction.sigma

namespace OMA.S_oeis_a114887

def IsMultiperfect (n : ℕ) : Prop :=
  ∃ k : ℕ, σ 1 n = k * n

def sumPrimeFactors (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p

def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ IsMultiperfect n ∧ sumPrimeFactors n ∣ n

theorem main : Set.Finite {n : ℕ | IsTerm n} := by
  sorry

end OMA.S_oeis_a114887
