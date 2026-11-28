import Mathlib.NumberTheory.Divisors

namespace OMA.S_oeis_a350142

/-- Number of positive divisors `τ(n)`. -/
def tau (n : ℕ) : ℕ :=
  n.divisors.card

/-- OEIS A350142 Conjecture 1: for every `k : ℕ`, the number `m = 2^k + 1` satisfies
`τ(m - 2) = τ(m - 1) - 1` if and only if `τ(m - 2) = k`. -/
theorem main :
    ∀ k : ℕ,
      let m := 2 ^ k + 1
      tau (m - 2) = tau (m - 1) - 1 ↔ tau (m - 2) = k := by
  sorry

end OMA.S_oeis_a350142
