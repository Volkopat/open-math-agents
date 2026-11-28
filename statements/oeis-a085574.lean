import Mathlib

/-!
# A085574: Least k such that n*(n+1)*(n+2) + k is palindromic.

Source: https://oeis.org/A085574
Credit: @EmircanEsen

Conjecture (OEIS A085574): For all n > 108, a(n) is > 1.

Formalization notes:
* Palindromic means in base 10: the decimal digits read the same backwards.
* `a n` is the least `k ≥ 0` with `n(n+1)(n+2) + k` palindromic (offset 1: `a 1 = 0`, since `6` is
  a palindrome, `a 2 = 9`, `a 3 = 6`). Such a `k` always exists (a number of the form `99…9` lies
  above any given number), so `sInf` is a true minimum.
* `a n > 1` means that neither `n(n+1)(n+2)` nor `n(n+1)(n+2) + 1` is a palindrome. Below
  `300000` the only `n` with `a n ≤ 1` are `1, 4, 7, 41, 77, 105, 108`.
-/

namespace OMA.S_oeis_a085574

/-- `m` is a palindrome in base 10. -/
def IsPalindrome (m : ℕ) : Prop := (Nat.digits 10 m).reverse = Nat.digits 10 m

/-- A085574: the least `k` such that `n(n+1)(n+2) + k` is a decimal palindrome. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | IsPalindrome (n * (n + 1) * (n + 2) + k)}

/-- For every `n > 108`, `a n > 1`. -/
theorem main : ∀ n : ℕ, 108 < n → 1 < a n := by
  sorry

end OMA.S_oeis_a085574
