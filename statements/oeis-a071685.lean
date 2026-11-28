import Mathlib

/-!
# A071685: Non-palindromic numbers n, not divisible by 10, such that either n divides R(n) or R(n) divides n

Source: https://oeis.org/A071685
Credit: @niclorusso

Conjecture (Harvey P. Dale, in the comments of A071685): every term mod 100 is equal to 1, 12, 78,
or 89.

Conventions:
* R(n) is the digit reversal of n in base 10: `Nat.ofDigits 10 (Nat.digits 10 n).reverse`
  (`Nat.digits 10 n` lists the decimal digits of n, least significant first).
* n is palindromic when R(n) = n.
* The terms are the positive n with R(n) /= n, n not divisible by 10, and n | R(n) or R(n) | n.
-/

namespace OMA.S_oeis_a071685

/-- The decimal digit reversal of `n`. -/
def R (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- `n` is a term of A071685. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ R n ≠ n ∧ ¬ 10 ∣ n ∧ (n ∣ R n ∨ R n ∣ n)

/-- Dale's conjecture on A071685: every term is congruent to 1, 12, 78 or 89 modulo 100. -/
theorem main : ∀ n : ℕ, IsTerm n → n % 100 ∈ ({1, 12, 78, 89} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a071685
