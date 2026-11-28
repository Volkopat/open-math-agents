import Mathlib

/-!
# A396018: the least `m` such that `m(m+1)(m+2)(m+3)(m+4)` has exactly `n` distinct prime factors

Source: https://oeis.org/A396018
Credit: @gblacher2

A396018: "Smallest number m such that m*(m+1)*(m+2)*(m+3)*(m+4) has exactly n distinct prime
factors." Offset 3. Data: a(3), a(4), ... = 1, 3, 7, 10, 19, 55, 91, 217, 493, 985, 1767, 7564,
24307, 44251, 99382, 357643, ...
Conjecture (in the entry): "a(n) is an increasing sequence."

Reading: `m` ranges over the positive integers (the data start at `m = 1`, and for `m = 0` the
product is `0`). The entry does not prove that `a(n)` exists for every `n ≥ 3`, so `main` states
the conjecture for the terms that exist, without adding an existence claim: whenever
`3 ≤ n < k` and both `a(n)` and `a(k)` exist (as least elements), `a(n) < a(k)`.

Checks: with this definition, the least `m ≤ 400000` for `n = 3, …, 18` are exactly the 16 terms
1, 3, 7, …, 357643 listed above (checked numerically).
-/

namespace OMA.S_oeis_a396018

/-- `m ≥ 1` and `m(m+1)(m+2)(m+3)(m+4)` has exactly `n` distinct prime factors. -/
def IsWitness (n m : ℕ) : Prop :=
  0 < m ∧ (m * (m + 1) * (m + 2) * (m + 3) * (m + 4)).primeFactors.card = n

/-- **A396018 conjecture.** The sequence is increasing: if `3 ≤ n < k` and `a(n)`, `a(k)` are the
least witnesses for `n` and `k` distinct prime factors, then `a(n) < a(k)`. -/
theorem main : ∀ n k : ℕ, 3 ≤ n → n < k → ∀ a b : ℕ,
    IsLeast {m : ℕ | IsWitness n m} a → IsLeast {m : ℕ | IsWitness k m} b → a < b := by
  sorry

end OMA.S_oeis_a396018
