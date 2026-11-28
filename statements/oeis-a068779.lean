import Mathlib

/-!
# A068779: Least number k such that floor( k / digit reversal of k ) = n.

Source: https://oeis.org/A068779
Credit: @rorcores

The entry (offset 1, data 1, 31, 51, 71, 120, 350, 230, 450, 890, 10, 650, 430, 320, 850, ...)
records in its COMMENTS section:

  Conjecture: every term after a(4) is a multiple of 10. - Harvey P. Dale, May 28 2015

Conventions:
* The digit reversal `R(k)` of a positive integer `k` is the number whose decimal digits are those
  of `k` in reverse order, leading zeros dropped (A004086); for example `R(120) = 21`. In Lean:
  `Nat.digits 10 k` lists the digits of `k` from the least significant one, and
  `Nat.ofDigits 10` of the reversed list is the reversed number.
* `a(n)` is the least positive integer `k` with `floor(k / R(k)) = n` (natural-number division `/`
  is the floor). The term `a(n)` is described by `IsTerm n a`: `a` is the least element of the set
  of such `k`.
* "Every term after a(4)" is every `a(n)` with `n ≥ 5`.
-/

namespace OMA.S_oeis_a068779

/-- The digit reversal of `k` in base 10 (A004086). -/
def digitReversal (k : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 k).reverse

/-- `a` is the term `a(n)` of A068779: the least positive `k` with
`floor(k / digitReversal k) = n`. -/
def IsTerm (n a : ℕ) : Prop := IsLeast {k : ℕ | 0 < k ∧ k / digitReversal k = n} a

/-- Dale's conjecture: every term after `a(4)` is a multiple of `10`. -/
theorem main : ∀ n a : ℕ, 5 ≤ n → IsTerm n a → 10 ∣ a := by
  sorry

end OMA.S_oeis_a068779
