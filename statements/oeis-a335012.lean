import Mathlib

/-!
# Repunit remainders and long-period primes

Source: Sen-Peng Eu, OEIS A335012 (2020), and the definition of the long
period primes in A006883, OEIS Foundation, CC BY-SA 4.0.
The index starts at 1. The first repunit has a single digit. A006883
includes 2 because the decimal expansion 0.5000... has periodic tail 0.
-/

namespace OMA.S_oeis_a335012

def repunit (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, 10^i

def countRemainders (n : ℕ) : ℕ :=
  ((Finset.range n).image fun j => (repunit (j+1) : ZMod n)).card

def isLongPeriodPrime (n : ℕ) : Prop :=
  n = 2 ∨ (n.Prime ∧ n.Coprime 10 ∧ orderOf (10 : ZMod n) = n-1)

theorem main : ∀ n : ℕ, 0<n → (countRemainders n = n-1 ↔ isLongPeriodPrime n) := by
  sorry

end OMA.S_oeis_a335012
