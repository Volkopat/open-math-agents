import Mathlib

/-!
# A common partial sum of the positive integers, primes, and nonprimes

Source: https://mathoverflow.net/questions/212985
Credit: @athemiz
-/

namespace OMA.S_mo_212985

open scoped BigOperators

/-- Sums of all positive integers through an integer endpoint. -/
def integerSums : Set ℤ :=
  Set.range fun n : ℤ => ∑ k ∈ Finset.Icc 1 n, k

/-- Sums of positive nonprimes, including 1, through a nonprime endpoint. -/
def nonprimeSums : Set ℤ :=
  {s | ∃ n : ℤ, ¬ n.toNat.Prime ∧
    s = ∑ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ k.toNat.Prime), k}

/-- Sums of positive primes through a prime endpoint. -/
def primeSums : Set ℤ :=
  {s | ∃ n : ℤ, n.toNat.Prime ∧
    s = ∑ k ∈ (Finset.Icc 2 n).filter (fun k => k.toNat.Prime), k}

theorem main : integerSums ∩ nonprimeSums ∩ primeSums = {28} := by
  sorry

end OMA.S_mo_212985
