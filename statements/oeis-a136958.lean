import Mathlib

/-!
# A136958: Numbers k such that k and k^2 use only the digits 0, 4, 7 and 8.

Source: https://oeis.org/A136958
Credit: @luciusacarr

The entry records two conjectures (Harvey P. Dale, Oct 24 2020). `main` states both, as a
conjunction, in the order the source gives them.

Conjecture 1. The digit 4 never appears in the terms of the sequence (although it does appear in
the digits of the squares of the terms, e.g. 878^2 = 770884).

Conjecture 2. All nonzero terms are of the form 88 * 10^m or 878 * 10^m.

Reading of the source:
* `k` is a term if every decimal digit of `k` and of `k^2` lies in {0, 4, 7, 8}. With
  `Nat.digits` the number `0` has no digits, so `0` is a term, as listed (offset 1, a(1) = 0).
* `m` ranges over the natural numbers. With this reading the terms below `10^7` are exactly 0, 88,
  878, 880, 8780, 8800, 87800, 88000, 878000, 880000, 8780000, 8800000.
-/

namespace OMA.S_oeis_a136958

/-- All decimal digits of `n` lie in {0, 4, 7, 8}. -/
def UsesDigits0478 (n : ℕ) : Prop := ∀ d ∈ Nat.digits 10 n, d = 0 ∨ d = 4 ∨ d = 7 ∨ d = 8

/-- `k` is a term of A136958. -/
def IsTerm (k : ℕ) : Prop := UsesDigits0478 k ∧ UsesDigits0478 (k ^ 2)

theorem main :
    -- Conjecture 1: no term has the digit 4.
    (∀ k : ℕ, IsTerm k → 4 ∉ Nat.digits 10 k) ∧
    -- Conjecture 2: every nonzero term is 88 * 10^m or 878 * 10^m.
    (∀ k : ℕ, IsTerm k → k ≠ 0 → ∃ m : ℕ, k = 88 * 10 ^ m ∨ k = 878 * 10 ^ m) := by
  sorry

end OMA.S_oeis_a136958
