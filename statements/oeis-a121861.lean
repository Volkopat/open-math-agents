import Mathlib

/-!
# A121861: least unused positive integer such that the partial sum plus one is prime.

Source: https://oeis.org/A121861
Credit: @cjchaffin

`a(n)` is the least previously nonoccurring positive integer such that
`a(1) + ⋯ + a(n) + 1` is prime. The sequence begins `1, 3, 2, 4, 6, 12, …`.

Conjecture (on the OEIS page): the sequence is `{1, 3}` union a permutation of the
positive even numbers, i.e. its image is exactly those values.

Conventions: offset 1.
-/

namespace OMA.S_oeis_a121861

def used (a : ℕ → ℕ) (n : ℕ) : Finset ℕ := (Finset.Icc 1 n).image a

def partialSum (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, a k

/-- A new positive integer `m` may be appended after `n` terms if `partialSum + m + 1` is prime. -/
def eligible (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  0 < m ∧ m ∉ used a n ∧ (partialSum a n + m + 1).Prime

/-- `a` is the greedy listing defined on the OEIS page. -/
def IsGreedy (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    eligible a n (a (n + 1)) ∧ ∀ m : ℕ, eligible a n m → a (n + 1) ≤ m

theorem main :
    ∃ a : ℕ → ℕ, IsGreedy a ∧
      ∀ k : ℕ, (k = 1 ∨ k = 3 ∨ (Even k ∧ 0 < k)) ↔ ∃ n : ℕ, 1 ≤ n ∧ a n = k := by
  sorry

end OMA.S_oeis_a121861
