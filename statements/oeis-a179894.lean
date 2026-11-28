import Mathlib

/-!
# A179894: Given the series (1, 2, 1, 2, 1, 2, ...), let (1 + 2x + x^2 + 2x^3 + ...) * (1 + 2x^2 + x^3 + 2x^4 + ...) = (1 + 2x + 3x^2 + 7x^3 + ...).

Source: https://oeis.org/A179894
Credit: @rickmanelius

Comment in the entry (unsigned; the entry is by Gary W. Adamson, Jul 31 2010): The offset has
been selected as 1 to accommodate the conjectured property of the sequence: 3 divides a(n) iff
n == 0 mod 3. Example: 3 divides (3, 12, 15, 27, 27, 42, ...) but not other terms through n = 18.
(Jon E. Schoenfield, Jul 31 2010, in the formula section: a(1) = 1; for odd n > 1,
a(n) = 2*n - 3; for even n, a(n) = 5*n/2 - 3. So it is true that 3 divides a(n) iff 3 divides n.)

Formalization notes:
* The first factor 1 + 2x + x^2 + 2x^3 + ... is the series (1, 2, 1, 2, ...): its coefficient
  of x^i is 1 for even i and 2 for odd i (`u`).
* The second factor 1 + 2x^2 + x^3 + 2x^4 + ... has coefficients 1, 0, 2, 1, 2, 1, ...: the
  coefficient of x^0 is 1, of x^1 is 0, and for j ≥ 2 the coefficient of x^j is 2 for even j and
  1 for odd j (`v`). This is the second factor of the Maple code of the entry,
  2*add(x^(2*n), n=0..50) - 1 + add(x^(2*n+1), n=0..50) - x.
* Both factors are power series with natural number coefficients (`PowerSeries.mk`). The
  product starts 1 + 2x + 3x^2 + 7x^3 + ..., and the offset is 1, so a(n) is the coefficient of
  x^(n-1) in the product. These definitions reproduce the 66 listed terms 1, 2, 3, 7, 7, 12, 11,
  17, ..., 127, 162 (checked by computer).
* The conjecture is stated for every n ≥ 1 (the offset), with n == 0 mod 3 read as n % 3 = 0.
  For n = 0 the natural-number subtraction would give a junk value; n = 0 is excluded.
-/

namespace OMA.S_oeis_a179894

/-- The series (1, 2, 1, 2, ...): the coefficient of x^i is 1 for even i and 2 for odd i. -/
def u (i : ℕ) : ℕ := if i % 2 = 0 then 1 else 2

/-- The coefficients 1, 0, 2, 1, 2, 1, ... of 1 + 2x^2 + x^3 + 2x^4 + ... -/
def v (j : ℕ) : ℕ := if j = 0 then 1 else if j = 1 then 0 else if j % 2 = 0 then 2 else 1

/-- 1 + 2x + x^2 + 2x^3 + ... -/
noncomputable def F : PowerSeries ℕ := PowerSeries.mk u

/-- 1 + 2x^2 + x^3 + 2x^4 + ... -/
noncomputable def G : PowerSeries ℕ := PowerSeries.mk v

/-- A179894(n) for n ≥ 1: the coefficient of x^(n-1) in F * G (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := PowerSeries.coeff (n - 1) (F * G)

/-- The conjecture: for n ≥ 1, 3 divides a(n) if and only if n == 0 (mod 3). -/
theorem main : ∀ n : ℕ, 1 ≤ n → (3 ∣ a n ↔ n % 3 = 0) := by
  sorry

end OMA.S_oeis_a179894
