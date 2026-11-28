import Mathlib

/-!
# A210393: least m > 1 making S_1!, ..., S_n! pairwise distinct modulo m

Source: https://oeis.org/A210393

A210393 (offset 1): `a(n)` is the least integer `m > 1` such that `S_k!` for `k = 1, …, n` are
pairwise distinct modulo `m`, where `S_k` is the sum of the first `k` primes:
2, 3, 7, 13, 19, 29, 43, 61, 79, 101, …  For example `a(3) = 7` since `2!`, `(2+3)!`,
`(2+3+5)!` are pairwise distinct modulo 7 but not modulo any of 2, 3, 4, 5, 6.

Conjecture (Zhi-Wei Sun, Mar 20 2012): `a(n)` is always a prime not exceeding `S_n`.

Conventions:
- `S k` is the sum of the first `k` primes, `∑ i ∈ Finset.range k, Nat.nth Nat.Prime i`
  (`S 1 = 2`, `S 2 = 5`, `S 3 = 10`, …).
- `IsAdmissible n m` says that `m > 1` and the factorials `(S k)!` for `1 ≤ k ≤ n` are pairwise
  incongruent modulo `m`; `a(n)` is the least admissible `m`.
- The statement is: for every `n ≥ 1`, any `m` that is the least admissible modulus (`IsLeast`)
  is prime and satisfies `m ≤ S n`.
-/

namespace OMA.S_oeis_a210393

/-- The sum of the first `k` primes. -/
noncomputable def S (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- `m > 1` and the numbers `(S k)!`, `1 ≤ k ≤ n`, are pairwise distinct modulo `m`. -/
def IsAdmissible (n m : ℕ) : Prop :=
  1 < m ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → ¬ ((S i).factorial ≡ (S j).factorial [MOD m])

theorem main :
    ∀ n m : ℕ, 0 < n → IsLeast {m : ℕ | IsAdmissible n m} m → Nat.Prime m ∧ m ≤ S n := by
  sorry

end OMA.S_oeis_a210393
