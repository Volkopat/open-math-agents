import Mathlib

/-!
# A210394: least m > 1 dividing none of S_i! + S_j!

Source: https://oeis.org/A210394

A210394 (offset 1): `a(n)` is the least integer `m > 1` such that `m` divides none of
`S_i! + S_j!` with `0 < i < j ≤ n`, where `S_k` is the sum of the first `k` primes:
2, 3, 7, 11, 19, 31, 43, 67, 79, 101, …  For example `a(3) = 7`, since 7 divides none of
`2! + (2+3)!`, `2! + (2+3+5)!`, `(2+3)! + (2+3+5)!`, but this fails for `m = 2, 3, 4, 5, 6`.

Conjecture (Zhi-Wei Sun, Mar 20 2012): `a(n)` is always a prime not exceeding `S_n`.

Conventions:
- `S k` is the sum of the first `k` primes, `∑ i ∈ Finset.range k, Nat.nth Nat.Prime i`
  (`S 1 = 2`, `S 2 = 5`, `S 3 = 10`, …).
- `IsAdmissible n m` says that `m > 1` and `m` divides none of `(S i)! + (S j)!` with
  `1 ≤ i < j ≤ n`; `a(n)` is the least admissible `m`.
- The statement is: for every `n ≥ 1`, any `m` that is the least admissible modulus (`IsLeast`)
  is prime and satisfies `m ≤ S n`.
-/

namespace OMA.S_oeis_a210394

/-- The sum of the first `k` primes. -/
noncomputable def S (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- `m > 1` and `m` divides none of `(S i)! + (S j)!` with `1 ≤ i < j ≤ n`. -/
def IsAdmissible (n m : ℕ) : Prop :=
  1 < m ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → ¬ m ∣ (S i).factorial + (S j).factorial

theorem main :
    ∀ n m : ℕ, 0 < n → IsLeast {m : ℕ | IsAdmissible n m} m → Nat.Prime m ∧ m ≤ S n := by
  sorry

end OMA.S_oeis_a210394
