import Mathlib

/-!
# A401001: Numbers k such that the sum of digits of k in base b is not prime for any base b in the range 2 <= b <= floor(sqrt(k)).

Source: https://oeis.org/A401001
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A401001 (Guido Avagliano, Oct 12 2026): Conjectured to
be finite, with 1650 being the last term.

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 4, 8, 16, 64, 114, 190, 204, 294, 366, ...).
* The sum of digits of k in base b is the sum of the list `Nat.digits b k`. The range 2 <= b <=
  floor(sqrt(k)) is written as 2 <= b and b^2 <= k. The terms are the positive integers k such
  that this digit sum is not prime for every such b.
* `Finite, with 1650 being the last term` is stated as: every term is at most 1650.
-/

namespace OMA.S_oeis_a401001

/-- The conjecture recorded in A401001. -/
theorem main : ∀ k : ℕ, 0 < k →
    (∀ b : ℕ, 2 ≤ b → b ^ 2 ≤ k → ¬ (Nat.digits b k).sum.Prime) → k ≤ 1650 := by
  sorry

end OMA.S_oeis_a401001
