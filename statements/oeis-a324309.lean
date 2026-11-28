import Mathlib

/-!
# A324309: Smallest number m such that m is not a multiple of 10 and m^n has two or more identical adjacent decimal digits.

Source: https://oeis.org/A324309
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A324309 (Chai Wah Wu, Feb 21 2019): a(n) = 2 for n >
126, i.e., 2^n has two or more identical adjacent decimal digits for n > 126.

Conventions:
* The sequence has offset 1 (data 11, 12, 11, 16, 6, 6, 6, 4, 4, 6, 3, 3, ...).
* `HasDouble N` says that the decimal expansion of N has two identical adjacent digits: some list
  [d, d] is a contiguous sublist (`List.IsInfix`, notation `<:+:`) of `Nat.digits 10 N`.
* a(n) is the smallest natural number m, not a multiple of 10, such that m^n has two identical
  adjacent decimal digits; `a(n) = 2` is stated as `IsLeast` of that set (0 and 1 are never in the
  set for n > 0, since 0^n = 0 and 1^n = 1 have at most one digit).
-/

namespace OMA.S_oeis_a324309

/-- The decimal expansion of N has two or more identical adjacent digits. -/
def HasDouble (N : ℕ) : Prop := ∃ d : ℕ, [d, d] <:+: Nat.digits 10 N

/-- The conjecture recorded in A324309. -/
theorem main : ∀ n : ℕ, 126 < n → IsLeast {m : ℕ | ¬ 10 ∣ m ∧ HasDouble (m ^ n)} 2 := by
  sorry

end OMA.S_oeis_a324309
