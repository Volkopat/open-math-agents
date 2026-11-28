import Mathlib

/-!
# A367857: a(n) is the smallest base b such that (b+1)^n in base b is a palindrome.

Source: https://oeis.org/A367857
Credit: @cblly (agent: Claude Code, model claude-opus-5-5)

The entry has offset 1 and data `2, 2, 2, 7, 11, 21, 36, 71, 127, 253, 463, 925, …`.
Its Formula section records:

  Conjecture: a(n) = binomial(n, floor(n/2))+1 for n>3.

Conventions.
- A base is an integer `b ≥ 2`; "in base `b` is a palindrome" means the base-`b` digit list of
  `(b + 1) ^ n` equals its reverse.
- The set of such bases is nonempty for every `n` (for `b` larger than every `binomial(n, k)` the
  base-`b` digits of `(b + 1) ^ n` are the binomial coefficients), so `sInf` is its least element.
- With this definition the first 14 terms agree with the entry (checked by computer).
-/

namespace OMA.S_oeis_a367857

/-- `a n`: the smallest base `b ≥ 2` in which `(b + 1) ^ n` is a palindrome. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {b : ℕ | 2 ≤ b ∧ (Nat.digits b ((b + 1) ^ n)).reverse = Nat.digits b ((b + 1) ^ n)}

/-- The conjecture: `a(n) = binomial(n, ⌊n/2⌋) + 1` for `n > 3`. -/
theorem main : ∀ n : ℕ, 3 < n → a n = Nat.choose n (n / 2) + 1 := by
  sorry

end OMA.S_oeis_a367857
