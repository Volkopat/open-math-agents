import Mathlib

/-!
# A248133: Least positive integer m such that m + n divides T(m) + T(n), where T(.) is given by A002426.

Source: https://oeis.org/A248133
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A248133 (Zhi-Wei Sun, Oct 02 2014): a(n) exists for any
n > 0. Moreover, a(n) <= n^2 - n + 1 except for n = 274.

Conventions:
* The sequence has offset 1 (data 1, 3, 1, 1, 7, 2, 2, 2, 1, 1, 7, 4, ...).
* T(.) is the sequence A002426: the central trinomial coefficients T(n) = Sum_{k=0..floor(n/2)}
  C(n,2k)*C(2k,k) (1, 1, 3, 7, 19, 51, ...); this is the helper `T`.
* `a(n) exists` means that there is a positive integer m with the stated divisibility (then the
  least such m exists); it is stated directly as the existence of m, without defining a(n).
* `a(n) <= n^2 - n + 1` for the least such m is equivalent to the existence of such an m with m <=
  n^2 - n + 1, which is how the second sentence is stated; both sentences are combined into one
  statement: for every n > 0 there is such an m, and for n other than 274 there is one with m <=
  n^2 - n + 1. For n > 0 the subtraction n^2 - n is exact.
-/

namespace OMA.S_oeis_a248133

/-- A002426: the central trinomial coefficients T(n) = Sum_{k=0..floor(n/2)} C(n,2k)*C(2k,k). -/
def T (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 2 + 1), n.choose (2 * k) * (2 * k).choose k

/-- The conjecture recorded in A248133. -/
theorem main : ∀ n : ℕ, 0 < n → (∃ m : ℕ, 0 < m ∧ m + n ∣ T m + T n) ∧
    (n ≠ 274 → ∃ m : ℕ, 0 < m ∧ m ≤ n ^ 2 - n + 1 ∧ m + n ∣ T m + T n) := by
  sorry

end OMA.S_oeis_a248133
