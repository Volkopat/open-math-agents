import Mathlib

/-!
# A214196: Unique terms in sequence A210144

Source: https://oeis.org/A214196
Author: Zhi-Wei Sun (2012, Conjecture 1.5(i))

Conjecture (Zhi-Wei Sun, OEIS A214196 / A210144):
For every `n ≥ 1`, let `A210144(n)` be the least integer `m > 1` such that the first
`n` primorials `p_1#, p_2#, ..., p_n#` are pairwise distinct modulo `m`.
Then every term of `A210144` (and hence every unique term in `A214196`) is prime.

Conventions:
- `primorial k` is the product of the first `k` primes (`primorial 1 = 2`,
  `primorial 2 = 6`, `primorial 3 = 30`, ...).
- First terms of A210144 (`n ≥ 1`): `2, 3, 5, 11, 11, 23, 29, 37, 37, 41, 47, ...`.
- First terms of A214196: `2, 3, 5, 11, 23, 29, 37, 41, 47, 73, 131, 151, ...`.
-/

namespace OMA.S_oeis_a214196

/-- The `k`-th primorial `p_1 * p_2 * ... * p_k` (OEIS A002110). -/
noncomputable def primorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- Predicate stating that the first `n` primorials are pairwise distinct modulo `m`. -/
def PrimorialsDistinctMod (n m : ℕ) : Prop :=
  ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → primorial i % m ≠ primorial j % m

/-- Conjecture (Zhi-Wei Sun): for every `n ≥ 1`, the least `m > 1` making the first `n`
primorials pairwise distinct modulo `m` (A210144(n)) is prime. -/
theorem main :
    ∀ n m : ℕ, 1 ≤ n →
      IsLeast {k : ℕ | 1 < k ∧ PrimorialsDistinctMod n k} m →
      Nat.Prime m := by
  sorry

end OMA.S_oeis_a214196
