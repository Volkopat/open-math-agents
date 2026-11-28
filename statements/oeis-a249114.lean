import Mathlib

/-!
# A249114: Take the counting numbers and continue adding 1, 2, ..., a(n) until one reaches a fourth prime.

Source: https://oeis.org/A249114
Credit: @bnb9001

The sequence has offset 1. Following the entry's formula,
a(n) = Min{k > 0 | {n + A000217(j), j = 1..k} contains four primes}, where
A000217(j) = j (j + 1) / 2; the starting number `n` itself is not counted (a(1) = 7, a(2) = 6).
That a(n) exists for every n is only conjectural (Hardy and Littlewood's conjecture F), so `a` is
`sInf` of the admissible `k`, which is `0` if there is none.

Conjecture (Michel Marcus): the minimum value reached by a(n) is 6. Jon Perry notes that this is
true. We state it as: every admissible `k` for every `n ≥ 1` is at least 6, and some `n ≥ 1` has
a(n) = 6.
-/

namespace OMA.S_oeis_a249114

/-- The number of primes among `n + j (j + 1) / 2` for `1 ≤ j ≤ k`. -/
def primeCount (n k : ℕ) : ℕ :=
  ((Finset.Icc 1 k).filter (fun j => (n + j * (j + 1) / 2).Prime)).card

/-- A249114: the least `k > 0` such that `primeCount n k ≥ 4` (or `0` if none exists). -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ 4 ≤ primeCount n k}

/-- The minimum value of a(n) is 6: no `n ≥ 1` reaches four primes in fewer than 6 steps, and
some `n ≥ 1` has a(n) = 6. -/
theorem main : (∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 4 ≤ primeCount n k → 6 ≤ k) ∧
    ∃ n : ℕ, 1 ≤ n ∧ a n = 6 := by
  sorry

end OMA.S_oeis_a249114
