import Mathlib

/-!
# A371561: Numbers with multiplicative digital root of 5 that are free of 1s and have their digits in ascending order.

Source: https://oeis.org/A371561
Credit: @azmiozgen

Conjecture (from the entry; if a(20) exists it is > 10^500): the sequence is complete, i.e. its
terms are exactly 5, 35, 57, 355, 359, 557, 579, 3335, 3357, 5579, 5777, 33557, 35559, 333555, 357799,
557779, 3335779, 3355777, 33333577.

Formalization notes:
* The digit product map f(n) = product of the decimal digits fixes single digits and decreases
  n ≥ 10, so n has multiplicative digital root 5 iff f^[j] n = 5 for some j.
* "Digits in ascending order" allows repeats (e.g. 3335), i.e. the digits read from the left are
  nondecreasing; `Nat.digits` lists the least significant digit first, so its reverse is sorted (stated with `List.Pairwise (· ≤ ·)`).
* Controls (computed): among nondecreasing digit strings over 2..9 of length ≤ 14, those with
  multiplicative digital root 5 are exactly the 19 listed numbers.
-/

namespace OMA.S_oeis_a371561

/-- The product of the decimal digits of `n`. -/
def digitProd (n : ℕ) : ℕ := (Nat.digits 10 n).prod

/-- `n` is a term. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ (∃ j : ℕ, digitProd^[j] n = 5) ∧ 1 ∉ Nat.digits 10 n ∧
    (Nat.digits 10 n).reverse.Pairwise (· ≤ ·)

/-- The sequence is complete. -/
theorem main :
    {n : ℕ | IsTerm n} = ({5, 35, 57, 355, 359, 557, 579, 3335, 3357, 5579, 5777, 33557, 35559,
      333555, 357799, 557779, 3335779, 3355777, 33333577} : Set ℕ) := by
  sorry

end OMA.S_oeis_a371561
