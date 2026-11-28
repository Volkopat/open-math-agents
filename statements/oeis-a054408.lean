import Mathlib

/-!
# A054408: greedy positive integers whose partial sums are prime.

Source: https://oeis.org/A054408
Credit: @cjchaffin

`a(n)` is the smallest positive integer not already in the sequence such that the partial
sum `a(1) + ⋯ + a(n)` is prime. The sequence begins `2, 1, 4, 6, 10, …` (so `1` is the
only odd term).

Conjecture (N. J. A. Sloane, May 29 2017): every even number appears.

Conventions: offset 1; “every even number” means every positive even integer (the terms
themselves are positive).
-/

namespace OMA.S_oeis_a054408

def used (a : ℕ → ℕ) (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).image a

def partialSum (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, a k

/-- A positive integer `m` may be appended after `n` terms if it is new and the new sum is prime. -/
def eligible (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  0 < m ∧ m ∉ used a n ∧ (partialSum a n + m).Prime

/-- `a` is the greedy listing defined on the OEIS page. -/
def IsGreedy (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    eligible a n (a (n + 1)) ∧ ∀ m : ℕ, eligible a n m → a (n + 1) ≤ m

theorem main :
    ∃ a : ℕ → ℕ, IsGreedy a ∧ ∀ k : ℕ, Even k → 0 < k → ∃ n : ℕ, 1 ≤ n ∧ a n = k := by
  sorry

end OMA.S_oeis_a054408
