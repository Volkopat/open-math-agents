import Mathlib

/-!
# A348319: Perfect powers m^k, k >= 2 that are palindromes while m is not.

Source: https://oeis.org/A348319
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a348319

def IsDecimalPalindrome (n : ℕ) : Prop :=
  Nat.digits 10 n = (Nat.digits 10 n).reverse

theorem main : ∀ n k : ℕ, 1 < n → 5 ≤ k → ¬ IsDecimalPalindrome (n ^ k) := by
  sorry

end OMA.S_oeis_a348319
