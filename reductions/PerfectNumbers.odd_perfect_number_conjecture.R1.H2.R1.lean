import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R1

-- Reduction PerfectNumbers.odd_perfect_number_conjecture.R1.H2.R1 of step PerfectNumbers.odd_perfect_number_conjecture.R1.H2
-- Credit: @marcusbuffett

/-!
# Odd perfect numbers with least prime factor 5 to 17: few prime factors, and the open rest

The parent step says that no odd perfect number `n` has this least prime factor, which is part
of the odd perfect number problem.

* `H1` (elementary): an odd perfect number with least prime factor in `{5, 7, 11, 13, 17}` has at least six distinct prime factors. The divisor sum satisfies `σ(n) * ∏ (p - 1) ≤ n * ∏ p` over the
  primes dividing `n`, so a perfect `n` needs `2 * ∏ (p - 1) ≤ ∏ p`; for `r` distinct odd numbers
  `≥ m` the product of `p / (p - 1)` is at most `∏_{j<r} (m + 2j) / (m + 2j - 1)`, which is below
  `2` for `r ≤ 5`. (Bounds of this kind go back to Grün 1952.)
* `H2`: the case of more than `5` distinct prime factors, which stays open.
-/

namespace OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1

/-- At most `5` distinct prime factors. -/
def H1 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n → n.primeFactors.card ≤ 5 → Nat.minFac n ∉ ({5, 7, 11, 13, 17} : Set ℕ)

/-- The open part: more than `5` distinct prime factors. -/
def H2 : Prop :=
  ∀ n : ℕ, Nat.Perfect n → Odd n → 6 ≤ n.primeFactors.card → Nat.minFac n ∉ ({5, 7, 11, 13, 17} : Set ℕ)

theorem main : H1 → H2 → OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1.H2 := by
  intro h1 h2 n hperf hodd
  by_cases hc : n.primeFactors.card ≤ 5
  · exact h1 n hperf hodd hc
  · exact h2 n hperf hodd (by omega)

end OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H2_R1
