import Mathlib

/-!
# A008474: iterating n ↦ Σ (p_j + k_j) reaches 5

Source: https://oeis.org/A008474
Credit: @jagraj28

A008474: if `n = Product p_j^k_j` then `a(n) = Sum (p_j + k_j)` (so `a(1) = 0`). The entry
records a conjecture (Ivan N. Ianakiev, 2014): for `m > 4`, by iterating the map `m ↦ a(m)` one
always reaches 5 (tested up to `m = 320000`).

`main` states: for every `m > 4` some iterate of `a` at `m` equals 5.

Conventions: the sum runs over the distinct prime factors `p` of `n`, with `k` the exponent of
`p` in `n` (`Nat.factorization`). The cycle `5 → 6 → 7 → 8 → 5` shows that reaching 5 once
means returning to it forever. A check for `5 ≤ m ≤ 100000` finds no exception.
-/

namespace OMA.S_oeis_a008474

/-- `a n`, OEIS A008474: the sum of `p + k` over the prime powers `p^k` exactly dividing `n`. -/
def a (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, (p + n.factorization p)

/-- Ianakiev's conjecture in OEIS A008474. -/
theorem main : ∀ m : ℕ, 4 < m → ∃ k : ℕ, a^[k] m = 5 := by
  sorry

end OMA.S_oeis_a008474
