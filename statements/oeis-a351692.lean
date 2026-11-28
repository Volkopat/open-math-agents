import Mathlib

/-!
# A351692: least `k` with `prime(n) + 2 prime(n-k)` and `prime(n) + 2 prime(n+k)` prime

Source: https://oeis.org/A351692
Credit: @Lenqth

A351692(n) (offset 1) is the least `k` with `1 ≤ k < n` such that `prime(n) + 2 prime(n-k)` and
`prime(n) + 2 prime(n+k)` are both prime, or `0` if there is no such `k`. Here `prime(i)` is the
`i`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (i - 1)`. For example `a(6) = 3`, since
`13 + 2*5 = 23` and `13 + 2*23 = 59` are prime.

Formalizes the conjecture in the comments of A351692: `a(n) = 0` exactly for
`n = 1, 5, 7, 14, 16, 17, 18, 19, 33, 34, 43, 54, 77, 78, 80, 101, 127`.
-/

namespace OMA.S_oeis_a351692

/-- The `i`-th prime, `1`-indexed: `prime 1 = 2`. -/
noncomputable def prime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- `k` witnesses `a(n) ≠ 0`. -/
def IsWitness (n k : ℕ) : Prop :=
  1 ≤ k ∧ k < n ∧ (prime n + 2 * prime (n - k)).Prime ∧ (prime n + 2 * prime (n + k)).Prime

/-- The `n ≥ 1` with `a(n) = 0` are exactly the seventeen listed values. -/
theorem main : {n : ℕ | 1 ≤ n ∧ ¬ ∃ k, IsWitness n k} =
    {1, 5, 7, 14, 16, 17, 18, 19, 33, 34, 43, 54, 77, 78, 80, 101, 127} := by
  sorry

end OMA.S_oeis_a351692
