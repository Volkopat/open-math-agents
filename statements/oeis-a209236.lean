import Mathlib

/-!
# A209236: m with m-1, m+1 prime and m-2, m, m+2 practical

Source: https://oeis.org/A209236

A209236 (offset 1): the integers `m > 0` with `m-1` and `m+1` both prime, and `m-2`, `m`, `m+2`
all practical: 4, 6, 18, 30, 198, 462, 1482, 2550, 3330, 4422, …  For example 18 is a term since
`{17, 19}` is a twin prime pair and 16, 18, 20 are practical numbers.

Conjecture (Zhi-Wei Sun, Jan 13 2013): `a(n)` always exists. In other words, there are
infinitely many quintuples `(m-2, m-1, m, m+1, m+2)` with `m-1` and `m+1` both prime and `m-2`,
`m`, `m+2` all practical.

The conjecture is stated as: the set of such `m` is infinite.

Conventions:
- A positive integer `n` is practical if every `k ≤ n` is a sum of distinct divisors of `n`
  (1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30, …). This is the same definition as in the merged
  statements on practical numbers (for example oeis-a373615).
- Everything is in `ℕ`. Since `m - 1` is prime, `m ≥ 3`, so the subtractions are exact.
-/

namespace OMA.S_oeis_a209236

/-- A practical number: a positive integer `n` such that every `m ≤ n` is a sum of distinct
divisors of `n` (OEIS A005153). -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

theorem main :
    Set.Infinite {m : ℕ | Nat.Prime (m - 1) ∧ Nat.Prime (m + 1) ∧ IsPractical (m - 2) ∧
      IsPractical m ∧ IsPractical (m + 2)} := by
  sorry

end OMA.S_oeis_a209236
