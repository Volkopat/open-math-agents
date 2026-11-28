import Mathlib

/-!
# A073659: start at 1, then greedily take unused evens so that partial sums are prime.

Source: https://oeis.org/A073659
Credit: @cjchaffin

`a 1 = 1`; for `n > 1`, `a(n)` is the smallest even number not already in the sequence
such that `a(1) + ⋯ + a(n)` is prime. The sequence begins `1, 2, 4, 6, 10, …`.

Conjecture (N. J. A. Sloane, May 29 2017): every even number appears.

Conventions: offset 1; “even number” means a positive even integer (the rule itself
selects even numbers, hence excludes 0). The sequence is “essentially the same” as
A054408 (which starts `2, 1, 4, 6, …`).
-/

namespace OMA.S_oeis_a073659

def used (a : ℕ → ℕ) (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).image a

def partialSum (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, a k

/-- An unused positive even integer may be appended after `n` terms if the new sum is prime. -/
def eligible (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  0 < m ∧ Even m ∧ m ∉ used a n ∧ (partialSum a n + m).Prime

/-- `a` is the greedy listing defined on the OEIS page, starting at `a 1 = 1`. -/
def IsGreedy (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧
    ∀ n : ℕ, 1 ≤ n →
      eligible a n (a (n + 1)) ∧ ∀ m : ℕ, eligible a n m → a (n + 1) ≤ m

theorem main :
    ∃ a : ℕ → ℕ, IsGreedy a ∧ ∀ k : ℕ, Even k → 0 < k → ∃ n : ℕ, 1 ≤ n ∧ a n = k := by
  sorry

end OMA.S_oeis_a073659
