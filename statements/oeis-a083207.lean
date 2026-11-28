import Mathlib

/-!
# A083207: Zumkeller or integer-perfect numbers: numbers n whose divisors can be partitioned into two disjoint sets with equal sum.

Source: https://oeis.org/A083207
Credit: @luciusacarr

The entry's comments record three conjectures. `main` states all three, as a conjunction, in the
order the source gives them.

Conjecture 1 (T. D. Noe, Mar 31 2010). The 229026 Zumkeller numbers less than 10^6 have a maximum
difference of 12; conjecturally any 12 consecutive numbers include at least one Zumkeller number.

Conjecture 2 (Ivan N. Ianakiev, Apr 03 2017). Any 4 consecutive terms include at least one number
k such that sigma(k)/2 is also a Zumkeller number (verified for the first 10^5 Zumkeller numbers).

Conjecture 3 (Ivan N. Ianakiev, Apr 24 2020). If d > 1, d | k and tau(d)*sigma(d) = k, then k is
a Zumkeller number (cf. A331668).

Reading of the source:
* A positive integer `n` is Zumkeller if its set of divisors splits into two disjoint parts with
  equal sums, i.e. some subset `S` of the divisors has the same sum as its complement in the
  divisors. Both parts are then nonempty, since the divisor sum is positive. The terms are
  6, 12, 20, 24, 28, ... (1 is not a term: its only divisor cannot be split).
* Conjecture 1: "numbers" are positive integers; the 12 consecutive numbers are
  `n, n + 1, ..., n + 11` for `n ≥ 1`.
* Conjecture 2: the terms are listed in increasing order as `Nat.nth IsZumkeller i` (offset 0
  here; the offset does not matter for a claim about every window of 4 consecutive terms). For a
  Zumkeller number `k`, `sigma(k)` is even (it is twice the sum of either part), so `sigma(k)/2`
  is exact.
* Conjecture 3: `tau(d)` is the number of divisors of `d` and `sigma(d)` their sum; `d` and `k`
  range over the natural numbers.
-/

namespace OMA.S_oeis_a083207

/-- `n` is a Zumkeller number: `n > 0` and the divisors of `n` can be partitioned into two
disjoint sets with equal sum. -/
def IsZumkeller (n : ℕ) : Prop :=
  0 < n ∧ ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d

theorem main :
    -- Conjecture 1: any 12 consecutive positive integers include a Zumkeller number.
    (∀ n : ℕ, 1 ≤ n → ∃ k, n ≤ k ∧ k < n + 12 ∧ IsZumkeller k) ∧
    -- Conjecture 2: any 4 consecutive terms include a term k with sigma(k)/2 Zumkeller.
    (∀ i : ℕ, ∃ j, i ≤ j ∧ j < i + 4 ∧ IsZumkeller (ArithmeticFunction.sigma 1 (Nat.nth IsZumkeller j) / 2)) ∧
    -- Conjecture 3: if d > 1, d ∣ k and tau(d) * sigma(d) = k, then k is Zumkeller.
    (∀ d k : ℕ, 1 < d → d ∣ k → d.divisors.card * ArithmeticFunction.sigma 1 d = k → IsZumkeller k) := by
  sorry

end OMA.S_oeis_a083207
