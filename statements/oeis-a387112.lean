import Mathlib

/-!
# OEIS A387112

Source: https://oeis.org/A387112 (OEIS Foundation, CC BY-SA 4.0).
Gus Wiseman's sequence consists of the positive integers for which the initial
intervals of the prime indices, counted with multiplicity, admit distinct
representatives. Prime indices are one-based: the index of a prime p is the
number of primes at most p. Mathlib lists the prime factors in increasing order.
-/

namespace OMA.S_oeis_a387112

/-- The sorted prime indices of `n`, with one slot per prime factor. -/
def primeIndex (n : ℕ) (i : Fin n.primeFactorsList.length) : ℕ :=
  Nat.primeCounting (n.primeFactorsList.get i)

/-- Choose a different positive representative from each initial interval. -/
def Choosable (n : ℕ) : Prop :=
  ∃ f : Fin n.primeFactorsList.length → ℕ,
    Function.Injective f ∧ ∀ i, 1 ≤ f i ∧ f i ≤ primeIndex n i

/-- Wiseman's criterion for the sorted prime indices. -/
theorem main : ∀ n : ℕ, 0 < n →
    (Choosable n ↔ ∀ i : Fin n.primeFactorsList.length, i.val + 1 ≤ primeIndex n i) := by
  sorry

end OMA.S_oeis_a387112
