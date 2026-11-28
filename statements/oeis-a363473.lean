import Mathlib

/-!
# A363473: a triangle of prime multiples, conjecturally a permutation of the positive integers

Source: https://oeis.org/A363473
Credit: @avivorly

A363473 (offset 1): triangle read by rows: `T(n, k) = k * prime(n - k + A061395(k))` for `1 < k <= n`, and
`T(n, 1) = A008578(n)`.

Here `prime(i)` is the `i`-th prime (`prime(1) = 2`); A061395(k) is the index `π(gpf(k))` of the greatest prime factor of
`k`, with `A061395(1) = 0`; A008578 is `1` followed by the primes (`A008578(1) = 1`, `A008578(n) = prime(n - 1)` for `n ≥ 2`).

Conjecture (in the entry): this is a permutation of the natural numbers.

Generalized conjecture (in the entry): Let `T(n, k) = b(k) * prime(n - k + A061395(b(k)))` for `1 < k <= n`, and
`T(n, 1) = A008578(n)`, where `b(n)`, `n > 0`, is a permutation of the natural numbers with `b(1) = 1`, then `T(n, k)`,
read by rows, is a permutation of the natural numbers.

Conventions:
- "Natural numbers" are the positive integers, as in the data (`1, 2, 4, 3, 6, 9, 5, ...`, no `0`).
- The triangle is indexed by `(n, k)` with `1 ≤ k ≤ n` (%O 1). Reading by rows enumerates this index set bijectively, so
  "read by rows, a permutation of the natural numbers" is stated as: `(n, k) ↦ T(n, k)` is a bijection from the index set
  onto the positive integers (`Set.BijOn ... (Set.Ici 1)`), i.e. every positive integer occurs exactly once.
- `prime i = Nat.nth Nat.Prime (i - 1)` (`Nat.nth` is 0-indexed). `gpf k` is the largest element of `k.primeFactors`, and
  `0` for `k = 1` (no prime factors), so `A061395 k = Nat.primeCounting (gpf k)` gives `A061395 1 = 0`, as in the entry.
- In the generalized conjecture `b : ℕ → ℕ` is a permutation of the positive integers, `Set.BijOn b (Set.Ici 1) (Set.Ici 1)`
  (its value at `0` plays no role), with `b 1 = 1`.
- `main` states both: the conjecture for `A363473` exactly as defined in %N, and the generalized conjecture for every such
  `b` (the case `b = id` of the second is the first).
-/

namespace OMA.S_oeis_a363473

/-- `prime i` is the `i`-th prime, 1-indexed: `prime 1 = 2`, `prime 2 = 3`, `prime 3 = 5`, ... -/
noncomputable def prime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- The greatest prime factor of `k`, and `0` for `k = 1` (no prime factors). -/
def gpf (k : ℕ) : ℕ := k.primeFactors.sup id

/-- A061395: `A061395 k = π(gpf k)`, the index of the greatest prime factor of `k`; `A061395 1 = 0`. -/
def A061395 (k : ℕ) : ℕ := Nat.primeCounting (gpf k)

/-- A008578 (offset 1): `1` followed by the primes: `A008578 1 = 1`, `A008578 n = prime (n - 1)` for `n ≥ 2`. -/
noncomputable def A008578 (n : ℕ) : ℕ := if n = 1 then 1 else prime (n - 1)

/-- A363473: `T(n, k) = k * prime(n - k + A061395(k))` for `1 < k ≤ n`, and `T(n, 1) = A008578(n)`. -/
noncomputable def A363473 (n k : ℕ) : ℕ :=
  if k = 1 then A008578 n else k * prime (n - k + A061395 k)

/-- The generalized triangle for `b`: `T_b(n, k) = b(k) * prime(n - k + A061395(b(k)))` for `1 < k ≤ n`, and
`T_b(n, 1) = A008578(n)`. -/
noncomputable def Tb (b : ℕ → ℕ) (n k : ℕ) : ℕ :=
  if k = 1 then A008578 n else b k * prime (n - k + A061395 (b k))

theorem main :
    Set.BijOn (fun nk : ℕ × ℕ => A363473 nk.1 nk.2) {nk : ℕ × ℕ | 1 ≤ nk.2 ∧ nk.2 ≤ nk.1} (Set.Ici 1) ∧
      ∀ b : ℕ → ℕ, Set.BijOn b (Set.Ici 1) (Set.Ici 1) → b 1 = 1 →
        Set.BijOn (fun nk : ℕ × ℕ => Tb b nk.1 nk.2) {nk : ℕ × ℕ | 1 ≤ nk.2 ∧ nk.2 ≤ nk.1} (Set.Ici 1) := by
  sorry

end OMA.S_oeis_a363473
