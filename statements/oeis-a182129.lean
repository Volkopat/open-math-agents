import Mathlib

/-!
# A182129: iterations of n -> (sum of the decimal digits of n)^n needed to stabilize.

Source: https://oeis.org/A182129
Credit: @avivorly

A182129(n) counts the iterations of the map x ↦ (sum of the decimal digits of x)^n, starting at n,
before the trajectory reaches a value already in it (example in the entry, exponent 2 from 2:
2 → 4 → 16 → 49 → 169 → 256 → 169, so a(2) = 5).

Generalization and conjecture in the entry (Michel Lagneau, 2012): let k be a positive integer; the number
of iterations of the orbit k ↦ (sum of the decimal digits of k)^n is finite for any exponent n and any
starting value k. That is: for all n ≥ 1 and k ≥ 1, the trajectory of k under x ↦ (digit sum of x)^n
reaches a value it has already visited, i.e. two iterates coincide.
-/

namespace OMA.S_oeis_a182129

/-- The map x ↦ (sum of the decimal digits of x)^n. -/
def f (n x : ℕ) : ℕ := (Nat.digits 10 x).sum ^ n

theorem main : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∃ i j : ℕ, i < j ∧ (f n)^[i] k = (f n)^[j] k := by
  sorry

end OMA.S_oeis_a182129
