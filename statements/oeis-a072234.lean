import Mathlib

/-!
# A072234: Numbers k such that reverse(k) = sum of the proper divisors of k.

Source: https://oeis.org/A072234
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a072234

def reverseDecimal (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n).reverse

def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ reverseDecimal n = ∑ d ∈ n.properDivisors, d

theorem main : ∀ n : ℕ, IsTerm n → 3 ∣ n := by
  sorry

end OMA.S_oeis_a072234
