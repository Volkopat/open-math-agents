import Mathlib

/-!
# A214891: Numbers that are not the sum of two squares and two fourth powers.

Source: https://oeis.org/A214891
Credit: @prasledi

Conjecture (Zhi-Wei Sun, Jan 27 2022, in the COMMENTS of A214891): the set {a(n): n > 0}
coincides with {16^k*m: k = 0, 1, 2, ... and m = 23, 44, 71, 79, 184, 519, 599, 4024}.

Formalization notes:
* A natural number n is a sum of two squares and two fourth powers when
  n = a^2 + b^2 + c^4 + d^4 for some natural numbers a, b, c, d (zero allowed, as the
  OEIS data shows: 0 and every small number not in the list are such sums).
* The conjecture is stated as an equality of sets of natural numbers: the numbers that are
  NOT such sums are exactly the numbers 16^k * m with k >= 0 and m in the given list.
* A brute-force search confirms the equality for all n <= 200000.
-/

namespace OMA.S_oeis_a214891

/-- Sun's conjecture on A214891. -/
theorem main :
    {n : ℕ | ¬ ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + c ^ 4 + d ^ 4} =
      {n : ℕ | ∃ k : ℕ, ∃ m ∈ ({23, 44, 71, 79, 184, 519, 599, 4024} : Finset ℕ),
        n = 16 ^ k * m} := by
  sorry

end OMA.S_oeis_a214891
