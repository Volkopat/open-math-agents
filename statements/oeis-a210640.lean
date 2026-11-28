import Mathlib

/-!
# A210640: least m > 1 making 2*S_k^2, k = 1..n, pairwise distinct modulo m

Source: https://oeis.org/A210640

A210640 (offset 1): `a(n)` is the least integer `m > 1` such that `2*S_k^2` (`k = 1, …, n`) are
pairwise distinct modulo `m`, where `S_k` is the sum of the first `k` primes:
2, 4, 9, 13, 17, 28, 37, 37, 37, 37, 37, 61, …  For example `a(3) = 9`, because `8`, `50`, `200`
are pairwise distinct modulo 9 but not modulo any of 2, 3, 4, 5, 6, 7, 8.

Conjecture (Zhi-Wei Sun, Mar 26 2012): `a(n)` is a prime smaller than `n^2` unless `n` divides 6.

Conventions:
- `S k` is the sum of the first `k` primes, `∑ i ∈ Finset.range k, Nat.nth Nat.Prime i`
  (`S 1 = 2`, `S 2 = 5`, `S 3 = 10`, …).
- `IsAdmissible n m` says that `m > 1` and the numbers `2*(S k)^2` for `1 ≤ k ≤ n` are pairwise
  incongruent modulo `m`; `a(n)` is the least admissible `m`.
- The statement is: for every `n ≥ 1` that does not divide 6 (that is, `n` not in
  `{1, 2, 3, 6}`), any `m` that is the least admissible modulus (`IsLeast`) is prime and
  satisfies `m < n^2`.
-/

namespace OMA.S_oeis_a210640

/-- The sum of the first `k` primes. -/
noncomputable def S (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- `m > 1` and the numbers `2*(S k)^2`, `1 ≤ k ≤ n`, are pairwise distinct modulo `m`. -/
def IsAdmissible (n m : ℕ) : Prop :=
  1 < m ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → ¬ (2 * S i ^ 2 ≡ 2 * S j ^ 2 [MOD m])

theorem main :
    ∀ n m : ℕ, 0 < n → ¬ n ∣ 6 → IsLeast {m : ℕ | IsAdmissible n m} m →
      Nat.Prime m ∧ m < n ^ 2 := by
  sorry

end OMA.S_oeis_a210640
