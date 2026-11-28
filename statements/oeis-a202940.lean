import Mathlib

/-!
# A202940: Positive numbers n such that n is not a multiple of 10 and n^3 has at most three different digits.

Source: https://oeis.org/A202940
Credit: @azmiozgen

Conjecture (from the entry): no more terms other than those of the form 10^n+1, n = 0, 1, 2, ...

Formalization notes:
* The terms listed in the entry that are not of the form 10^k + 1 are 1, 3, 4, 5, 6, 7, 8, 9, 14, 15,
  36, 62, 92, 173, 192, 211, 888, 3543, 110011, 146796. The conjecture is stated as: every term is
  one of these or of the form 10^k + 1.
* "At most three different digits" is `(Nat.digits 10 (n ^ 3)).toFinset.card ≤ 3`.
* Controls (computed): the terms below 3*10^6 are exactly 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 14, 15, 36,
  62, 92, 101, 173, 192, 211, 888, 1001, 3543, 10001, 100001, 110011, 146796, 1000001, as in the entry.
-/

namespace OMA.S_oeis_a202940

/-- Every term is a listed exceptional term or `10^k + 1`. -/
theorem main :
    ∀ n : ℕ, 0 < n → ¬ 10 ∣ n → (Nat.digits 10 (n ^ 3)).toFinset.card ≤ 3 →
      n ∈ ({1, 3, 4, 5, 6, 7, 8, 9, 14, 15, 36, 62, 92, 173, 192, 211, 888, 3543, 110011, 146796} :
        Finset ℕ) ∨ ∃ k : ℕ, n = 10 ^ k + 1 := by
  sorry

end OMA.S_oeis_a202940
