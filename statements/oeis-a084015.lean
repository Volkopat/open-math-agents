import Mathlib

/-!
# A084015: Largest n-digit palindromic multiple of n

Source: https://oeis.org/A084015
Credit: @gaudinfrederic

A084015(n) is the largest n-digit multiple of `n` that is palindromic; for
`n = 10 * k` the multiple only needs to be palindromic once leading zeros are
ignored. The entry is `0` when no such multiple exists.

Conjecture (the OEIS comment): no entry is zero — for every `n ≥ 1` there is an
n-digit palindromic multiple of `n`.

## Encoding

* "n-digit" means `(Nat.digits 10 N).length = n`.
* "palindromic with leading zeros ignored" means
  `List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0))`: decimal digits are
  stored least-significant first, so dropping leading zeros of the written form
  is dropping the zeros at the front of the digit list.
* `a_val n` is the largest element of the finite filtered set, or `0` if the
  set is empty (`Finset.sup` on `ℕ` returns `0` on `∅`).
-/

namespace OMA.S_oeis_a084015

/-- `N` is palindromic in base 10 once leading zeros of its written form are
ignored. -/
abbrev isPal (N : ℕ) : Prop :=
  List.Palindrome ((Nat.digits 10 N).dropWhile (· = 0))

/-- `a_val n`: largest `n`-digit palindromic multiple of `n`, or `0` if none. -/
def a_val (n : ℕ) : ℕ :=
  ((Finset.range (10 ^ n)).filter
    (fun N => n ∣ N ∧ (Nat.digits 10 N).length = n ∧ isPal N)).sup id

/-- The conjecture on A084015: no entry is zero. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 0 < a_val n := by
  sorry

end OMA.S_oeis_a084015
