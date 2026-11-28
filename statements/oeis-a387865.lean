import Mathlib

/-!
# A387865: even numbers as two consecutive primes plus a practical number

Source: https://oeis.org/A387865

A387865 (offset 1): `a(n)` is the number of ways to write `2*n` as `p + p' + q`, where `p` is a
prime, `p'` is the first prime after `p`, and `q` is a practical number:
0, 0, 1, 0, 1, 1, 2, 2, 1, 3, …  For example `a(3) = 1` with `2 + 3 + 1 = 2*3`, and `a(5) = 1`
with `3 + 5 + 2 = 2*5`.

Conjecture (Zhi-Wei Sun, Oct 15 2025): `a(n) > 0` for all `n > 4`. In other words, any even
number not smaller than 10 is the sum of two consecutive primes and a practical number. The
entry notes that this has been verified for all `n = 5..10^6`.

Since `a(n)` counts the triples `(p, p', q)` with `p` prime, `p'` the next prime after `p`, `q`
practical and `p + p' + q = 2n`, `a(n) > 0` says exactly that such a triple exists, and the
conjecture is stated in that form.

Conventions:
- `p'` is the first prime after `p`: `p'` is prime, `p < p'`, and no prime lies strictly between
  `p` and `p'`.
- A positive integer `q` is practical if every `m ≤ q` is a sum of distinct divisors of `q`
  (1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30, …). This is the same definition as in the merged
  statements on practical numbers (for example oeis-a373615). In particular `1` is practical, as
  in the entry's example for `a(3)`.
-/

namespace OMA.S_oeis_a387865

/-- A practical number: a positive integer `n` such that every `m ≤ n` is a sum of distinct
divisors of `n` (OEIS A005153). -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

/-- `p'` is the first prime after the prime `p`. -/
def IsNextPrime (p p' : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime p' ∧ p < p' ∧ ∀ r : ℕ, p < r → r < p' → ¬ Nat.Prime r

theorem main :
    ∀ n : ℕ, 4 < n →
      ∃ p p' q : ℕ, IsNextPrime p p' ∧ IsPractical q ∧ p + p' + q = 2 * n := by
  sorry

end OMA.S_oeis_a387865
