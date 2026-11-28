import Mathlib

/-!
# A354852: mixed radix representations of a prime and of its predecessor

Source: https://oeis.org/A354852
Credit: @avivorly

OEIS A354852 (%N, verbatim): a(n) is the number of distinct ways to represent n using any mixed radix numeral system.

Claim (%F, verbatim): Conjecture: a(p) = a(p-1)+1 whenever p is a prime number.

Conventions:
- A way to represent `n` is a digit string `d_1 d_2 ... d_k` (`k ≥ 1`, most significant digit `d_1` first, every digit
  a natural number, leading digit `d_1 ≥ 1`) for which some radices `b_2, ..., b_k ≥ 2` with `d_i < b_i`
  (`2 ≤ i ≤ k`) give `n = (...((d_1 * b_2 + d_2) * b_3 + d_3) ...) * b_k + d_k`. The radix `b_1` of the leading digit
  does not enter the value and any `b_1 > d_1` may be taken, so the leading digit is unbounded (the entry lists the
  one-digit string 5 with radix 6, and its example string 101 with radices 2, 2, 2 has value `(1*2 + 0)*2 + 1 = 5`).
- Distinct ways are distinct digit strings, not distinct pairs of a string and radices: the entry lists the six strings
  101, 10, 11, 12, 21, 5 for `a(5) = 6`, and `a(6) = 8` counts the string 100 once although the radices `(2, 3)` and
  `(3, 2)` both give `6`. With this reading a computable copy of the definitions below gives the entry's terms
  `a(1), ..., a(30)`.
- In Lean a digit string is a `l : List ℕ` written least significant digit first, as `Nat.digits` writes digits:
  `[d_k, ..., d_2, d_1]`. `Rep l n` is the Horner recursion for the value: a one-digit string `[d]` represents `n`
  exactly when `d ≠ 0` and `d = n`; a string `d :: ds` with `ds` nonempty represents `n` exactly when its leading part
  `ds` (the digits `d_1 ... d_{k-1}`) represents some `m` and `n = d + b * m` for some radix `b ≥ 2` with `d < b`.
  Unfolding the recursion gives the displayed formula, with `b` running through `b_k, ..., b_2`. The empty list
  represents nothing.
- `a n` is the `Set.ncard` of the set of strings that represent `n`. As `Set.ncard` of an infinite set is `0`, `main`
  also asserts that each of these sets is finite, so the counts are the true counts.
- `p - 1` is natural subtraction, exact here since a prime is `≥ 2`.
-/

namespace OMA.S_oeis_a354852

/-- `Rep l n`: the digit string `l` (least significant digit first, so its leading digit is the last entry) represents
`n` in some mixed radix numeral system. A one-digit string `[d]` represents `d` when `d ≠ 0`; a longer string
`d :: ds` represents `d + b * m` when its leading part `ds` represents `m` and the radix `b ≥ 2` exceeds the digit
`d`. -/
def Rep : List ℕ → ℕ → Prop
  | [], _ => False
  | [d], n => d ≠ 0 ∧ d = n
  | d :: e :: ds, n => ∃ b m : ℕ, 2 ≤ b ∧ d < b ∧ Rep (e :: ds) m ∧ n = d + b * m

/-- `a n` (A354852): the number of distinct digit strings that represent `n` in some mixed radix numeral system. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {l : List ℕ | Rep l n}

theorem main :
    (∀ n : ℕ, {l : List ℕ | Rep l n}.Finite) ∧
      ∀ p : ℕ, p.Prime → a p = a (p - 1) + 1 := by
  sorry

end OMA.S_oeis_a354852
