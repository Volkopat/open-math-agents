import Mathlib

/-!
# OEIS A006883 and Artin's conjectured density in base ten

OEIS A006883 includes the prime 2 because the repeating tail of 1/2 is zero.
For primes coprime to ten, the decimal period of 1/p is the multiplicative
order of ten modulo p. The other terminating case is p = 5, whose period
is one and hence smaller than p - 1.

Source: OEIS Foundation, A006883, https://oeis.org/A006883 (CC BY-SA 4.0).
Density formula recorded by Gerard Schildberger, 2005.
-/

namespace OMA.S_oeis_a006883

open Filter
open scoped Topology BigOperators

def LongPeriodPrime (p : ℕ) : Prop :=
  p.Prime ∧ (p = 2 ∨ (p.Coprime 10 ∧ orderOf (10 : ZMod p) = p - 1))

noncomputable def primeProportion (n : ℕ) : ℝ := by
  classical
  let s := Finset.range (n + 1)
  exact ((s.filter LongPeriodPrime).card : ℝ) / ((s.filter Nat.Prime).card : ℝ)

theorem main :
    Tendsto primeProportion atTop
      (𝓝 (∏' q : Nat.Primes,
        (1 - 1 / (((q : ℕ) : ℝ) * (((q : ℕ) : ℝ) - 1))))) := by
  sorry

end OMA.S_oeis_a006883
