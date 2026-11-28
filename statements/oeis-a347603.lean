import Mathlib

/-!
# A347603: Numbers k such that tau(k) = 2*tau(k-1) and sigma(k) = sigma(k-1), where tau(k) and sigma(k) are respectively the number and sum functions of the divisors of k.

Source: https://oeis.org/A347603
Credit: @luciusacarr

Data: 4365, 74919, 79827, 111507, 347739, 445875, 739557, 2168907, 4481986, 7263945, ...

Conjecture (from the entry): the asymptotic density of terms is equal to 0 and this sequence is
infinite. `main` states both parts, as a conjunction, in the order the source gives them.

Reading of the source:
* `tau(k)` is the number of divisors `(Nat.divisors k).card` and `sigma(k)` their sum; `k`
  ranges over `k ≥ 2`, so that `k - 1` is a positive integer.
* "Asymptotic density 0" is stated as: the proportion `#{k ∈ S : k ≤ N} / N` tends to 0 as
  `N → ∞`.
-/

namespace OMA.S_oeis_a347603

/-- The terms of A347603. -/
def S : Set ℕ :=
  {k | 2 ≤ k ∧ (Nat.divisors k).card = 2 * (Nat.divisors (k - 1)).card ∧
    ArithmeticFunction.sigma 1 k = ArithmeticFunction.sigma 1 (k - 1)}

theorem main :
    -- The asymptotic density of the terms is 0.
    Filter.Tendsto (fun N : ℕ => ((Set.ncard {k ∈ S | k ≤ N} : ℕ) : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) ∧
    -- The sequence is infinite.
    S.Infinite := by
  sorry

end OMA.S_oeis_a347603
