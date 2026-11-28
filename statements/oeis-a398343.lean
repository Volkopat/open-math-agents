import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Nat.Squarefree

/-!
# Finite multiplicities of the radical quotient in A398343

A398342 lists the positive integers k for which the sum of the radicals
of its divisors is divisible by rad(k), once each in increasing order.
Thus a value m occurs finitely often precisely when the displayed set of
positive integers k is finite. We clear the positive denominator rad(k).

Source: https://oeis.org/A398343 and https://oeis.org/A398342
Credit: @CubeJerry
-/

namespace OMA.S_oeis_a398343

open Finset

def rad : ArithmeticFunction ℕ :=
  ⟨fun n => if n=0 then 0 else ∏ p ∈ n.primeFactors, p, by simp⟩

theorem main : ∀ m : ℕ,
    {k : ℕ | 0<k ∧ (∑ d ∈ k.divisors, rad d) = m * rad k}.Finite := by
  sorry

end OMA.S_oeis_a398343
