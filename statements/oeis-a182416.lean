import Mathlib

/-!
# The Carmichael-number property recorded in OEIS A182416

Source: https://oeis.org/A182416
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A182/A182416.seq
Credit: @Heart-galaxy

This states the sufficient prime conditions for the three displayed
factors and the failure of their necessity. The parameter k ranges over
the nonnegative integers, as in the OEIS example with k = 0.

A Carmichael number is a composite integer greater than one that satisfies
the Fermat congruence for every base coprime to it. Charles R. Greathouse IV
notes that the conjecture follows from Korselt's criterion.
-/

namespace OMA.S_oeis_a182416

open Finset

def p (k : ℕ) : ℕ := 60 * k + 13

def q (k : ℕ) : ℕ := 180 * k + 37

def r (k : ℕ) : ℕ := 300 * k + 61

def N (k : ℕ) : ℕ := p k * q k * r k

def AllPrime (k : ℕ) : Prop := (p k).Prime ∧ (q k).Prime ∧ (r k).Prime

def Carmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]

theorem main : (∀ k : ℕ, AllPrime k → Carmichael (N k)) ∧
    ∃ k : ℕ, Carmichael (N k) ∧ ¬ AllPrime k := by
  sorry

end OMA.S_oeis_a182416
