import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.PrimeFin

/-!
# Squarefree kernel versus number of divisors (OEIS A070226)

Source: https://oeis.org/A070226 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @thomasfredrickson.

A070226 lists the numbers k whose squarefree kernel A007947(k) (the product
of the distinct primes dividing k) equals the number of divisors A000005(k).
C. O. Zizka's conjecture in the comments: if A000005(k) divides A007947(k)
for some k, then A007947(k) = A000005(k). Both functions are defined for
k >= 1, which is the range stated here.
-/

namespace OMA.S_oeis_a070226

/-- A007947: the squarefree kernel (radical) of `k`. -/
def rad (k : ℕ) : ℕ := ∏ p ∈ k.primeFactors, p

/-- A000005: the number of divisors of `k`. -/
def tau (k : ℕ) : ℕ := k.divisors.card

theorem main : ∀ k : ℕ, 1 ≤ k → tau k ∣ rad k → rad k = tau k := by
  sorry

end OMA.S_oeis_a070226
