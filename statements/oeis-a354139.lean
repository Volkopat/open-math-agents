import Mathlib

/-!
# A354139: the least window length whose sums of `n`-th powers are all divisible by `n`

Source: https://oeis.org/A354139
Credit: @avivorly

A354139: `a(n)` is the least positive integer `m` such that
`(k+1)^n + (k+2)^n + ... + (k+m)^n == 0 (mod n)` for every positive integer `k`. Offset 1.

A007947(n) is the squarefree kernel of `n`: the product of the distinct primes dividing `n`.

A193267(n) is the number 1 alternating with the numbers A006953/A002445. The entry's comment
(Peter Luschny) gives the explicit form used here: `A193267(n)` is the product over all prime powers
`p^e`, where `p^e` is the highest power of `p` dividing `n` and `p-1` divides `n`.

Conjecture (in the entry A354139): `a(n) = A007947(n) * A193267(n)`.

Conventions:
- `n ≥ 1` (offset 1); `k` ranges over the positive integers and the window sum
  `(k+1)^n + ... + (k+m)^n` is `∑ i ∈ Finset.Icc 1 m, (k + i) ^ n`.
- `a n` is the `sInf` of the set of valid positive `m`. For `n ≥ 1` the set is nonempty (the entry
  notes that `a(n)` divides `n * A007947(n)`), so `sInf` is its least element.
- A007947 is Mathlib's `UniqueFactorizationMonoid.radical` on `ℕ`, which equals
  `∏ p ∈ n.primeFactors, p` (`Nat.radical_eq_prod_primeFactors`).
- A193267 is Luschny's product form from the entry's comment: the product of
  `p ^ n.factorization p` over the primes `p ∣ n` with `(p - 1) ∣ n` (by von Staudt-Clausen and the
  denominator formula for `B_k / k`, this is the quotient A006953/A002445 at even `n`, and `1` at odd
  `n`); it reproduces the 100 listed terms of A193267.
-/

namespace OMA.S_oeis_a354139

/-- A354139: the least positive `m` such that `n` divides `(k+1)^n + ... + (k+m)^n` for every
positive integer `k`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ∀ k : ℕ, 0 < k → n ∣ ∑ i ∈ Finset.Icc 1 m, (k + i) ^ n}

/-- A007947: the squarefree kernel (radical) of `n`. -/
noncomputable def A007947 (n : ℕ) : ℕ := UniqueFactorizationMonoid.radical n

/-- A193267: the product of the prime powers `p ^ e` exactly dividing `n` with `(p - 1) ∣ n`. -/
def A193267 (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with (p - 1) ∣ n, p ^ n.factorization p

theorem main : ∀ n : ℕ, 1 ≤ n → a n = A007947 n * A193267 n := by
  sorry

end OMA.S_oeis_a354139
