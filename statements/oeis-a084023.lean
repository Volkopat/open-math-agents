import Mathlib

/-!
# OEIS A084023

`A084022(n)` is the largest `n`-digit multiple of `n` whose decimal digit
sum is also a multiple of `n` and which becomes palindromic once its
trailing zeros are ignored, or `0` when no such multiple exists;
`A084023(n) = A084022(n) / n`. Murthy and Srikanth conjectured in 2003
that no term is zero, i.e. that such a palindromic multiple exists for
every `n >= 1`, forcing the quotient to be at least `1`.

In the DATA-validated encoding, the number of ignored trailing zeros is
the decimal valuation `v10(n)` of `n` itself: a witness is
`N = P * 10^z` with `z = tz n`, the digit list of `P` a palindrome
(`Nat.digits` is little-endian, so the stripped zeros sit at the head of
the list), `len(P) + z = n` digits in total, `n | N` and
`n | sigma(P)`. Every witness is an `n`-digit number, hence bounded by
`10^n`, and `sSup` returns the largest element, with `sSup` of the empty
set equal to `0`, matching the `or 0 if no such number exists`
convention. Non-vanishing of the term is equivalent to the witness set
being nonempty, the form under which the conjecture is proved in the
DemosMathNT package.

Source: https://oeis.org/A084023
-/

namespace OMA.S_oeis_a084023

/-- Number of trailing zeros of `n` in base `10`, read on the
    little-endian digit list: the decimal valuation `v10(n)`. -/
def tz (n : ℕ) : ℕ := ((Nat.digits 10 n).takeWhile (· = 0)).length

/-- `N` is admissible for `n` when `N = P * 10^z` with `z = tz n`
    ignored trailing zeros, `P` a nonzero palindrome with
    `len(P) + z = n` digits in total, `n | N` and `n | sigma(P)`. -/
def qualifies (n N : ℕ) : Prop :=
  ∃ P z : ℕ, P ≠ 0
    ∧ z = tz n
    ∧ (Nat.digits 10 P).Palindrome
    ∧ (Nat.digits 10 P).length + z = n
    ∧ N = P * 10 ^ z
    ∧ n ∣ N
    ∧ n ∣ (Nat.digits 10 P).sum

/-- `A084022(n)`: the largest admissible multiple, `0` if none exists. -/
noncomputable def a084022 (n : ℕ) : ℕ := sSup {N | qualifies n N}

/-- `A084023(n)`: the quotient `A084022(n) / n`. -/
noncomputable def term (n : ℕ) : ℕ := a084022 n / n

/-- The Murthy-Srikanth conjecture: no term of `A084023` is zero. -/
theorem main : ∀ n : ℕ, 0 < n → term n ≠ 0 := by
  sorry

end OMA.S_oeis_a084023
