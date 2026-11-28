import Mathlib

/-!
# A187054: Numbers that are not the sum of three powerful numbers (A001694).

Source: https://oeis.org/A187054
Credit: @luciusacarr

Data: 1, 2, 4, 5, 7, 8, 15, 23, 31, 87, 111, 119.

The entry says: Heath-Brown shows that this sequence is finite, resolving a conjecture of Erdős.
Presumably a(12) = 119 is the last term. `main` states that conjecture: every number greater
than 119 is a sum of three powerful numbers.

Reading of the source:
* A001694 (powerful numbers) are the positive integers `m` such that `p^2 ∣ m` for every prime
  `p ∣ m` (1, 4, 8, 9, 16, ...); 0 is not powerful.
* The three summands need not be distinct (3 = 1 + 1 + 1 is not a term).
* With this reading the terms up to 5000 are exactly the twelve listed (checked numerically), so
  "119 is the last term" is the claim that every `n > 119` is a sum of three powerful numbers.
-/

namespace OMA.S_oeis_a187054

/-- A001694: `m` is powerful if `m > 0` and `p^2 ∣ m` for every prime `p` dividing `m`. -/
def IsPowerful (m : ℕ) : Prop := 0 < m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

theorem main :
    -- a(12) = 119 is the last term: every n > 119 is a sum of three powerful numbers.
    ∀ n : ℕ, 119 < n → ∃ a b c : ℕ, IsPowerful a ∧ IsPowerful b ∧ IsPowerful c ∧
      n = a + b + c := by
  sorry

end OMA.S_oeis_a187054
