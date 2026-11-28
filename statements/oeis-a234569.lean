import Mathlib

/-!
# A234569: Primes p with P(p-1) also prime, where P(.) is the partition function (A000041).

Source: https://oeis.org/A234569
Credit: @gblacher2

Formalizes the OEIS comment (Zhi-Wei Sun): "By the conjecture in A234567, this sequence should
have infinitely many terms. It seems that a(n+1) < a(n) + a(n-1) for all n > 5."

Conventions:
* `P(m)` is the number of partitions of `m` (A000041: 1, 1, 2, 3, 5, 7, 11, ...), here
  `Fintype.card (Nat.Partition m)`. For a prime `p` we have `p ≥ 2`, so `p - 1` does not truncate.
* `a(n)` is the `n`-th term of the sequence in increasing order, 1-indexed as in the OEIS
  (`a(1) = 3`, `a(2) = 5`, `a(3) = 7`), i.e. `Nat.nth (· ∈ S) (n - 1)` in Mathlib's 0-indexed
  convention.
* The two sentences of the comment are stated as a conjunction: the set of terms is infinite, and
  `a(n+1) < a(n) + a(n-1)` for every `n > 5`.
-/

namespace OMA.S_oeis_a234569

/-- The partition function `P(m)`. -/
def P (m : ℕ) : ℕ := Fintype.card (Nat.Partition m)

/-- The terms of A234569: primes `p` such that `P(p - 1)` is prime. -/
def S : Set ℕ := {p | p.Prime ∧ (P (p - 1)).Prime}

/-- `a n`: the `n`-th term of A234569, 1-indexed, so `a 1 = 3`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (· ∈ S) (n - 1)

/-- A234569 has infinitely many terms, and `a(n+1) < a(n) + a(n-1)` for all `n > 5`. -/
theorem main : S.Infinite ∧ ∀ n : ℕ, 5 < n → a (n + 1) < a n + a (n - 1) := by
  sorry

end OMA.S_oeis_a234569
