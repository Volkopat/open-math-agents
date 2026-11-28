import Mathlib

/-!
# OEIS A267084: a(n) = 0 if n divides the sum of the first n primes, 1 otherwise

Source: https://oeis.org/A267084
Credit: @unserus

OEIS: "It is conjectured that there are infinitely many zeros, but that their
density is zero."

a(n) = ceiling(A007504(n)/n) - floor(A007504(n)/n) (n ≥ 1), where
A007504(n) = p_1 + ... + p_n is the sum of the first `n` primes. So a(n) = 0
exactly when `n ∣ A007504(n)` (n = 1, 23, 53, 853, ..., A045345). The `i`-th
prime (0-indexed) is `Nat.nth Nat.Prime i`, so
`A007504(n) = ∑ i ∈ Finset.range n, Nat.nth Nat.Prime i`.

Both parts are stated, as a conjunction: the set of zeros is infinite, and its
natural density is 0 (the proportion of zeros among `1, ..., N` tends to 0).
-/

namespace OMA.S_oeis_a267084

/-- A007504(n): the sum of the first `n` primes. -/
noncomputable def sumPrimes (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, Nat.nth Nat.Prime i

/-- The zeros of A267084: the `n ≥ 1` dividing the sum of the first `n` primes. -/
def zeroSet : Set ℕ := {n | 1 ≤ n ∧ n ∣ sumPrimes n}

/-- A267084 has infinitely many zeros, and the zeros have density 0. -/
theorem main :
    zeroSet.Infinite ∧
      Filter.Tendsto
        (fun N : ℕ => ((Nat.card {n : ℕ // n ∈ zeroSet ∧ n ≤ N} : ℕ) : ℝ) / N)
        Filter.atTop (nhds 0) := by
  sorry

end OMA.S_oeis_a267084
