import Mathlib

/-!
# OEIS A342348: Smallest number > 3 with only digits 0-3 in all bases 2..n

Source: https://oeis.org/A342348
Credit: @unserus

OEIS: "Conjecture: there are no more terms." and (Bert Dobbelaere, Mar 14 2021)
"If it exists, a(10) > 10^2000."

a(n) (n ≥ 2) is the smallest number `m > 3` whose representation in every base
`b` with `2 ≤ b ≤ n` uses only the digits 0, 1, 2, 3. The known terms are
a(2..9) = 4, 4, 4, 5, 6, 7, 8, 8281. "No more terms" means a(10) does not exist:
no `m > 3` has all its digits at most 3 in every base from 2 to 10. (Any later
term a(n), n ≥ 10, would also be such an `m`, so this covers the whole tail.)
-/

namespace OMA.S_oeis_a342348

/-- `m` has only the digits 0, 1, 2, 3 in every base `b` with `2 ≤ b ≤ n`. -/
def SmallDigits (n m : ℕ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → b ≤ n → ∀ d ∈ Nat.digits b m, d ≤ 3

/-- There is no `m > 3` with only digits 0-3 in all bases 2 to 10. -/
theorem main : ¬ ∃ m : ℕ, 3 < m ∧ SmallDigits 10 m := by
  sorry

end OMA.S_oeis_a342348
