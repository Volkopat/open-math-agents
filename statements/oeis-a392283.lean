import Mathlib

/-!
# OEIS A392283

Conjecture: the terms of A392283 (numbers `k` such that `φ(k)` divides `k + 3`)
after 9 are identical to A039777.

Reading: both sequences are increasing lists of natural numbers, so "the terms
after 9 coincide" means that, for every `m > 9`, `m` is in A392283 exactly when
`m` is in A039777. A039777 has no term strictly between 9 and 21.

Sources: https://oeis.org/A392283 and https://oeis.org/A039777
Credit: @gblacher2
-/

namespace OMA.S_oeis_a392283

open scoped BigOperators

/-- The defining property of A039777: `φ(m)` equals the product of the distinct
prime factors of `m - 1` plus the product of the exponents in the prime
factorization of `m - 1` (OEIS example: `21 - 1 = 2^2 * 5`, `10 + 2 = 12 = φ(21)`).
It is only used for `m > 9`, so `m - 1 ≥ 9`. -/
def satisfiesA039777 (m : ℕ) : Prop :=
  let factors := (m - 1).factorization
  m.totient = (∏ p ∈ factors.support, p) + (∏ p ∈ factors.support, factors p)

theorem main :
    ∀ m : ℕ, 9 < m → ((m.totient ∣ m + 3) ↔ satisfiesA039777 m) := by
  sorry

end OMA.S_oeis_a392283
