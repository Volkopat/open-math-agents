import Mathlib

/-!
# A186080: fourth powers that are palindromic in base 10

Source: https://oeis.org/A186080
Credit: @Lenqth

A186080 lists the fourth powers `k^4` whose decimal expansion is a palindrome:
`0, 1, 14641, 104060401, 1004006004001, ...`, i.e. `k = 0, 1, 11, 101, 1001, ...`.

Formalizes the conjecture in the comments of A186080: if `k^4` is a palindrome `> 0`, then `k`
begins and ends with the digit `1` and all other digits of `k` are `0`. Such `k` are exactly
`k = 1` and `k = 10^m + 1` for `m ≥ 1` (`11, 101, 1001, ...`).

A natural number is a decimal palindrome when its list of decimal digits equals its reverse
(`Nat.digits` has no leading zeros, so this is the usual notion).
-/

namespace OMA.S_oeis_a186080

/-- `x` is a palindrome in base 10. -/
def IsPalindrome (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

/-- If `k^4` is a positive decimal palindrome, then `k = 1` or `k = 10^m + 1` with `m ≥ 1`. -/
theorem main : ∀ k : ℕ, 0 < k → IsPalindrome (k ^ 4) → k = 1 ∨ ∃ m : ℕ, 1 ≤ m ∧ k = 10 ^ m + 1 := by
  sorry

end OMA.S_oeis_a186080
