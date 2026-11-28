import Mathlib

/-!
# A159578: Infinitely many primorials divisible by the sum of their prime factors

Sources: https://oeis.org/A159578 and https://oeis.org/A051838.
The OEIS entry uses products of initial primes, starting at 2, in the question
on consecutive primes raised by Alladi and Erdős (1977), p. 290.
-/

namespace OMA.S_oeis_a159578

/-- The sum of the first `k` primes, starting at 2. -/
noncomputable def primeSum (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- The product of the first `k` primes, starting at 2. -/
noncomputable def primeProduct (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

theorem main :
    Set.Infinite {n : ℕ | ∃ k : ℕ, 0 < k ∧ n = primeProduct k ∧ primeSum k ∣ n} := by
  sorry

end OMA.S_oeis_a159578
