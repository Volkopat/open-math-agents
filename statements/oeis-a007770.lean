import Mathlib

/-!
# A007770: Happy numbers

Source: https://oeis.org/A007770
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Happy numbers are the numbers whose trajectory under iteration of the sum-of-squares-of-digits
map includes `1`. OEIS: it is conjectured that the sequence includes infinitely many primes
(the happy primes, A035497).

## Encoding

* The map is `n ↦ ∑ d², d` ranging over the decimal digits of `n` (`Nat.digits 10`).
* `n` is happy if some iterate of the map (starting from `n ≥ 1`) equals `1`.
* The other items in the same OEIS comment are elementary facts and are not stated here.
-/

namespace OMA.S_oeis_a007770

/-- Sum of the squares of the decimal digits. -/
def sumSqDigits (n : ℕ) : ℕ := ((Nat.digits 10 n).map fun d => d ^ 2).sum

/-- `n` is a happy number. -/
def IsHappy (n : ℕ) : Prop := 1 ≤ n ∧ ∃ k : ℕ, sumSqDigits^[k] n = 1

theorem main : {p : ℕ | p.Prime ∧ IsHappy p}.Infinite := by
  sorry

end OMA.S_oeis_a007770
