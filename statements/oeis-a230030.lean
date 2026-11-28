import Mathlib

/-!
# A230030: Numbers k not divisible by 5 such that k^2 written in base 5 has no digit > 1.

Source: https://oeis.org/A230030
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A230030 (David Radcliffe, May 01 2015): a(k) =
P(5^(k-2)) for every k > 5.

Conventions:
* The sequence has offset 1 (data 1, 972799, 3051273374, 6132750376, 839228035909, 3818357814376,
  2384643515634376, 1490173338867234376, 931329727148437734376, 582077503203735352734376,
  363797992467864990240234376, ...).
* Here P(x) = 25x^4 + 15x^3 - 4x^2 + 3x + 1, as defined in the preceding comment of the entry. In
  the statement the value P(5^(k-2)) is written with the subtraction last (25x^4 + 15x^3 + 3x + 1
  - 4x^2), which is exact in the natural numbers.
* The terms are the natural numbers k not divisible by 5 such that all base-5 digits of k^2
  (`Nat.digits 5 (k^2)`) are at most 1 (predicate `T`); a(k) is `Nat.nth T (k - 1)` (`Nat.nth` is
  0-indexed, the sequence has offset 1).
-/

namespace OMA.S_oeis_a230030

/-- k is a term of A230030: k is not divisible by 5 and k^2 has no base-5 digit > 1. -/
def T (k : ℕ) : Prop := ¬ 5 ∣ k ∧ ∀ d ∈ Nat.digits 5 (k ^ 2), d ≤ 1

/-- The conjecture recorded in A230030. -/
theorem main : ∀ k : ℕ, 5 < k → Nat.nth T (k - 1) =
    25 * (5 ^ (k - 2)) ^ 4 + 15 * (5 ^ (k - 2)) ^ 3 + 3 * 5 ^ (k - 2) + 1 -
      4 * (5 ^ (k - 2)) ^ 2 := by
  sorry

end OMA.S_oeis_a230030
