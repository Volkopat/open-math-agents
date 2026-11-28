import Mathlib

/-!
# A209320: 2n = p + q with p, q prime and p + 1, q - 1 practical

Source: https://oeis.org/A209320

A209320 (offset 1): `a(n)` is the number of ways to write `2n = p + q` with `p` and `q` both
prime, and `p + 1` and `q - 1` both practical numbers (A005153): 0, 0, 1, 2, 3, 2, 2, 2, 2, 3, …
For example `a(8) = 2` since `16 = 3 + 13 = 11 + 5` with `3 + 1`, `13 - 1`, `11 + 1`, `5 - 1` all
practical.

Conjecture (Zhi-Wei Sun, Jan 19 2013): `a(n) > 0` for all `n > 2`. The entry notes that, as
`p + q = (p + 1) + (q - 1)`, this unifies Goldbach's conjecture and its analog for practical
numbers, and that it has been verified for `n` up to `10^7`.

Since `a(n)` counts the pairs of primes `(p, q)` with `p + q = 2n` and `p + 1`, `q - 1`
practical, `a(n) > 0` says exactly that such a pair exists, and the conjecture is stated in that
form.

Conventions:
- A positive integer `n` is practical if every `m ≤ n` is a sum of distinct divisors of `n`
  (1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30, …). This is the same definition as in the merged
  statements on practical numbers (for example oeis-a373615).
- The condition is not symmetric in `p` and `q`, and no ordering between them is imposed (the
  listed terms count ordered pairs, as in the example for `a(8)`).
- Everything is in `ℕ`; `q - 1` is an exact subtraction because `q` is prime.
-/

namespace OMA.S_oeis_a209320

/-- A practical number: a positive integer `n` such that every `m ≤ n` is a sum of distinct
divisors of `n` (OEIS A005153). -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

theorem main :
    ∀ n : ℕ, 2 < n →
      ∃ p q : ℕ, p + q = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧ IsPractical (p + 1) ∧
        IsPractical (q - 1) := by
  sorry

end OMA.S_oeis_a209320
