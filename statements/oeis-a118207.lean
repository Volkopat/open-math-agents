import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Data.Nat.Factors

/-!
# Bala's Liouville and cyclotomic product identity

Source: https://oeis.org/A118207
Credit: @blakestone-x

A(X) is the product of (1+X^k) raised to the Liouville sign of k.
The conjecture identifies A(X^2) with the product of the cyclotomic pairs.
We state equality modulo X^(N+1) for every N, clearing the factors of
negative exponent. All cleared factors have constant coefficient one.
Factors indexed above N contribute only their constant term at this precision.
-/

namespace OMA.S_oeis_a118207

open Polynomial

noncomputable def positiveFactors (N : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range N, if Even (j+1).primeFactorsList.length
    then 1 + X^(2*(j+1)) else 1

noncomputable def negativeFactors (N : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range N, if Odd (j+1).primeFactorsList.length
    then 1 + X^(2*(j+1)) else 1

noncomputable def pairedFactors (N : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range N,
    (cyclotomic (j+1) ℚ).comp (X^(j+1)) *
    (cyclotomic (j+1) ℚ).comp ((-X)^(j+1))

theorem main : ∀ N : ℕ, (X : ℚ[X])^(N+1) ∣
    positiveFactors N - negativeFactors N * pairedFactors N := by
  sorry

end OMA.S_oeis_a118207
