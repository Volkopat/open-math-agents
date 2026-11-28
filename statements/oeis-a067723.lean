import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Totient

namespace OMA.S_oeis_a067723

/-- A positive integer is a base-10 palindrome if its base-10 digit list equals its reverse. -/
def IsPalindrome (k : ℕ) : Prop :=
  (Nat.digits 10 k).reverse = Nat.digits 10 k

/-- A nontrivial base-10 palindrome has at least 2 digits (i.e. `10 ≤ k`). -/
def IsTerm (k : ℕ) : Prop :=
  10 ≤ k ∧ IsPalindrome k ∧ IsPalindrome (Nat.totient k)

/-- Conjecture (OEIS A067723): there are no terms with an even number of decimal digits. -/
theorem main : ∀ k : ℕ, IsTerm k → ¬ Even (Nat.digits 10 k).length := by
  sorry

end OMA.S_oeis_a067723
