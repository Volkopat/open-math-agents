import Mathlib

/-!
# A133907: Least prime number p such that binomial(n+p, p) mod p = 1

Source: https://oeis.org/A133907

The sequence (offset 1) is `a(n)` = the least prime number `p` such that
`binomial(n+p, p) mod p = 1`; first terms `2, 3, 5, 2, 2, 7, 11, 2, 2, 3, 3, 2, 2, 17, 17, ...`.

Claim (comment of Thomas Ordowski, Jul 29 2018), in OEIS notation:
`Conjecture: a(n) is the smallest prime p such that Sum_{k=1..n} k^(p-1) == n (mod p).`
`Thus a(n) >= A317358(n).`
Here A317358(n) (offset 1) is the smallest number `k > 1` such that
`1^(k-1) + 2^(k-1) + ... + n^(k-1) == n (mod k)`.

The quoted text makes two claims, stated together here in the order of the entry:

1. `a(n)` is the smallest prime `p` with `Sum_{k=1..n} k^(p-1) == n (mod p)`;
2. the consequence drawn from it, `a(n) >= A317358(n)`.

The entry does not say that the conjecture has been proved. The other comments of the entry (the
description as the least prime `p` such that `p` divides `floor(n/p)` or `p > n`, and Robert Israel's
characterization of `a(n) = 2`) are presented as facts and are not part of the target.

Formalized:
* `a n` follows the name line literally: the infimum in `ℕ` of the set of primes `p` with
  `(n + p).choose p % p = 1` (`%` is the remainder of natural numbers). The infimum of the empty set
  of naturals is `0`; the set is never empty (every prime `p > n` belongs to it), so `a n` is its
  least element, but that fact is not built into the definition.
* `powerSum n k` is `1^(k-1) + 2^(k-1) + ... + n^(k-1)` as an integer, the sum over `1 <= j <= n`.
  It is only used with `k >= 2`, where the natural-number subtraction `k - 1` is exact.
* `A317358 n` follows the name line of A317358 literally: the infimum in `ℕ` of the set of `k > 1`
  with `powerSum n k == n (mod k)`.
* A congruence between integers is written with `Int.ModEq` (`x ≡ y [ZMOD m]`).
* Claim 1 is `IsLeast S (a n)` for the set `S` of primes `p` with `powerSum n p == n (mod p)`: `a n`
  belongs to `S` (in particular it is a prime) and is a lower bound of `S`. This cannot hold through
  the junk value `0` of an empty infimum.
* Claim 2 is the inequality `A317358 n ≤ a n` of natural numbers.
* The range is `n >= 1`, the offset of both sequences.
-/

namespace OMA.S_oeis_a133907

/-- A133907 (offset 1): the least prime number `p` such that `binomial(n+p, p) mod p = 1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ (n + p).choose p % p = 1}

/-- `1^(k-1) + 2^(k-1) + ... + n^(k-1)`, the sum over `1 <= j <= n`, as an integer. -/
def powerSum (n k : ℕ) : ℤ := ∑ j ∈ Finset.Icc 1 n, (j : ℤ) ^ (k - 1)

/-- A317358 (offset 1): the smallest number `k > 1` such that
`1^(k-1) + 2^(k-1) + ... + n^(k-1) == n (mod k)`. -/
noncomputable def A317358 (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 < k ∧ powerSum n k ≡ (n : ℤ) [ZMOD (k : ℤ)]}

/-- Ordowski: `a(n)` is the smallest prime `p` such that `Sum_{k=1..n} k^(p-1) == n (mod p)`;
thus `a(n) >= A317358(n)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      IsLeast {p : ℕ | p.Prime ∧ powerSum n p ≡ (n : ℤ) [ZMOD (p : ℤ)]} (a n) ∧
        A317358 n ≤ a n := by
  sorry

end OMA.S_oeis_a133907
