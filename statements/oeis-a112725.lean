import Mathlib

/-!
# A112725: Smallest positive palindromic multiple of 3^n.

Source: https://oeis.org/A112725

Conjecture recorded in the entry (Farideh Firoozbakht, Nov 12 2005), due to Jud McCranie
(stated in A062567, Aug 07 2001):
for n > 1, A062567(3^n) = 10^3^(n-2) - 1.

The entry itself explains that this conjecture will be rejected, since a(n) is much smaller
than 10^3^(n-2) - 1 for 4 < n <= 18 and A062567(3^n) <= a(n).

Formalization notes:
* The conjecture is a statement about A062567, so that is the sequence defined here, by the
  name of its entry: the first multiple of n whose reverse is also divisible by n, or 0 if no
  such multiple exists. Offset 1.
* First multiple is read as the least positive multiple k of n (the data begin
  a(1) = 1, so 0 is not counted). It is taken with `sInf` on the natural numbers, which is the
  least element of the set when it is nonempty and 0 when it is empty, exactly the convention
  of the entry.
* The reverse of k is the number whose decimal digits are those of k in reverse order, with
  leading zeros dropped (so the reverse of 10 is 1). It is computed with `Nat.digits 10` and
  `Nat.ofDigits 10`.
* 10^3^(n-2) is read as 10^(3^(n-2)), the number written with 3^(n-2) nines. For n > 1 the
  natural-number subtractions n - 2 and 10^(3^(n-2)) - 1 are exact.
-/

namespace OMA.S_oeis_a112725

/-- The decimal reverse of k: its digits in reverse order, leading zeros dropped. -/
def rev (k : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 k).reverse

/-- A062567: the first multiple of n whose reverse is also divisible by n,
or 0 if no such multiple exists. -/
noncomputable def A062567 (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ n ∣ k ∧ n ∣ rev k}

/-- McCranie's conjecture, as recorded in A112725: for n > 1, A062567(3^n) = 10^(3^(n-2)) - 1. -/
theorem main : ∀ n : ℕ, 1 < n → A062567 (3 ^ n) = 10 ^ (3 ^ (n - 2)) - 1 := by
  sorry

end OMA.S_oeis_a112725
