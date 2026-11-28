import Mathlib

/-!
# A386893: Farey fractions that are not similarly ordered

Source: https://oeis.org/A386893

Two fractions p/q and r/s are similarly ordered if (p - r)(q - s) >= 0. If
p_1/q_1, p_2/q_2, ... is the increasing sequence of Farey fractions of order n, then A386893(n)
(offset 4) is the largest integer m such that p_k/q_k and p_l/q_l are similarly ordered for all
k < l with l - k <= m. (The source writes p_l/q_k, a typo for p_l/q_l: with it, a(4) = 2, as
in the example: 1/4 and 2/3 are the only pair of fractions of order 4 that are not similarly
ordered.) Terms: 2, 3, 3, 4, 3, 3, 4, 5, ...
Its formula section states the conjecture (van Doorn, 2025): for all n >= 92,
a(n) = floor(n/4) + d, where d is either 1, 2, 2 or 4, depending on whether n is congruent to
0, 1, 2, or 3 modulo 4.
This is an exact form of the asymptotic a(n) = (1/4 + o(1)) n (Erdős Problem 1005).

Conventions:
* The Farey fractions of order n are the rationals x with 0 <= x <= 1 and denominator at most n,
  each written in lowest terms (`x.num / x.den`); `fareyList n` lists them increasingly.
* a(n) is `sSup` of the set of admissible m. For n >= 4 there is a pair that is not similarly
  ordered, so the set is bounded, and it contains 0, so `sSup` is its maximum.
-/

namespace OMA.S_oeis_a386893

/-- The Farey fractions of order `n`, in increasing order. -/
def fareyList (n : ℕ) : List ℚ :=
  ((Finset.Icc 1 n).biUnion (fun q => (Finset.range (q + 1)).image (fun p : ℕ => (p : ℚ) / q))).sort
    (· ≤ ·)

/-- The fractions `x` and `y` (in lowest terms) are similarly ordered. -/
def SimilarlyOrdered (x y : ℚ) : Prop := 0 ≤ (x.num - y.num) * ((x.den : ℤ) - y.den)

/-- A386893. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ k l : ℕ, (hk : k < l) → (hl : l < (fareyList n).length) → l - k ≤ m →
    SimilarlyOrdered ((fareyList n)[k]) ((fareyList n)[l])}

/-- For `n ≥ 92`, `a n = n / 4 + d (n % 4)` with `d = 1, 2, 2, 4`. -/
theorem main : ∀ n : ℕ, 92 ≤ n →
    a n = n / 4 + (if n % 4 = 0 then 1 else if n % 4 = 3 then 4 else 2) := by
  sorry

end OMA.S_oeis_a386893
