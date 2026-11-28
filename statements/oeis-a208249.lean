import Mathlib

/-!
# A208249: primes p with n < p < 2n such that p - 1 and p + 1 are both practical

Source: https://oeis.org/A208249

A208249 (offset 1): `a(n)` is the number of primes `p` with `n < p < 2n` such that `p - 1` and
`p + 1` are both practical numbers (A005153): 0, 1, 1, 2, 1, 1, 0, 0, 1, 2, 2, 2, …  For example
`a(9) = 1` since 17 is the only prime `9 < p < 18` with `p - 1` and `p + 1` both practical.

Conjecture (Zhi-Wei Sun, Jan 12 2013): `a(n) > 0` for all `n > 8`.

Since `a(n)` counts the primes `p` with `n < p < 2n` and `p - 1`, `p + 1` practical, `a(n) > 0`
says exactly that such a prime exists, and the conjecture is stated in that form. The four
further conjectures (1)-(4) listed afterwards in the entry are separate claims and are not part
of this statement.

Conventions:
- A positive integer `n` is practical if every `m ≤ n` is a sum of distinct divisors of `n`
  (1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30, …). This is the same definition as in the merged
  statements on practical numbers (for example oeis-a373615).
- Everything is in `ℕ`; `p - 1` is an exact subtraction because `p` is prime.
-/

namespace OMA.S_oeis_a208249

/-- A practical number: a positive integer `n` such that every `m ≤ n` is a sum of distinct
divisors of `n` (OEIS A005153). -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

theorem main :
    ∀ n : ℕ, 8 < n →
      ∃ p : ℕ, n < p ∧ p < 2 * n ∧ Nat.Prime p ∧ IsPractical (p - 1) ∧ IsPractical (p + 1) := by
  sorry

end OMA.S_oeis_a208249
