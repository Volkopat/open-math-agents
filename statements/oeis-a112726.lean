import Mathlib

/-!
# A112726: First positive multiple of 3^n whose reverse is also a multiple of 3^n.

Source: https://oeis.org/A112726

Conjecture in the entry (Jud McCranie, Aug 07 2001, recorded in A062567 and quoted in this
entry by Farideh Firoozbakht, Nov 13 2005):
for n>1, a(n)=10^3^(n-2)-1, that is, a(n) is the number written with 3^(n-2) nines.

Formalization notes:
* Offset 0. The claim is made for every n > 1, so the natural-number subtraction n - 2 is
  exact. The value 10^(3^(n-2)) - 1 is computed in the natural numbers, where it is exact
  because 10^(3^(n-2)) ≥ 1. The power tower 10^3^(n-2) is read as 10^(3^(n-2)), as the entry
  says (3^(n-2) nines).
* The sequence is defined by the name of the entry. The reverse of m is the number whose
  decimal digits are those of m in the opposite order, with leading zeros dropped, as in the
  Mathematica program of the entry (FromDigits of the reversed IntegerDigits).
* a(n) is the least m > 0 such that 3^n divides m and 3^n divides the reverse of m. It is taken
  with `sInf` on the natural numbers, which is the least element of the set when the set is
  nonempty. The entry notes the set is never empty, since 10^3^(n-2) - 1 belongs to it for
  n > 1 (and 1, 3 belong to it for n = 0, 1).
* The entry itself says that this conjecture is rejected for n > 4, and that it seems to hold
  only for n = 2, 3 and 4. The statement below is the conjecture as written.
-/

namespace OMA.S_oeis_a112726

/-- The decimal reverse of m. -/
def rev (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 m).reverse

/-- A112726: the first positive multiple of 3^n whose reverse is also a multiple of 3^n. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ 3 ^ n ∣ m ∧ 3 ^ n ∣ rev m}

/-- McCranie's conjecture on A112726: a(n) = 10^(3^(n-2)) - 1 for n > 1. -/
theorem main : ∀ n : ℕ, 1 < n → a n = 10 ^ (3 ^ (n - 2)) - 1 := by
  sorry

end OMA.S_oeis_a112726
