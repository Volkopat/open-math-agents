import Mathlib

/-!
# A324036: Modified reduced Collatz map fs acting on positive odd integers.

Source: https://oeis.org/A324036
Credit: @JeremyDevs

Formalizes the conjecture of Colin Barker (Oct 14 2019) recorded in OEIS A324036:
a(n) = 2*a(n-4) - a(n-8) for n>7.

Conventions:
* The sequence has offset 0 and a(n) = fs(1 + 2*n), where the map fs on the positive odd
  integers is given by the explicit formula of the entry (its Formula section, and the comment
  that the advantage of fs is an explicit formula): a(n) = (2 + 3*n)/2 if n == 0 (mod 4),
  a(n) = 2 + 3*n if n == 1 or 3 (mod 4), and a(n) = n/2 if n == 2 (mod 4). Equivalently
  fs(1 + 8*k) = 1 + 6*k, fs(3 + 8*k) = 5 + 12*k, fs(5 + 8*k) = 1 + 2*k, fs(7 + 8*k) = 11 + 12*k.
  The two divisions by 2 are exact (the numerators are even in those residue classes), so
  natural-number division renders them faithfully. Terms: 1, 5, 1, 11, 7, 17, 3, 23, 13, ...
* The recurrence has a negative coefficient, so both sides are compared in `ℤ`. For `n > 7` the
  indices `n - 4` and `n - 8` are genuine (no truncation).
* Barker's other conjecture, the generating function
  (1 + 5*x + x^2 + 11*x^3 + 5*x^4 + 7*x^5 + x^6 + x^7) / ((1 - x)^2*(1 + x)^2*(1 + x^2)^2), is not
  stated separately: its denominator is (1 - x^4)^2 = 1 - 2*x^4 + x^8, so given the first eight
  terms it is the same assertion as the recurrence for n > 7.
-/

namespace OMA.S_oeis_a324036

/-- A324036 (offset 0): a(n) = fs(2n+1), by the explicit formula in terms of n mod 4. -/
def a (n : ℕ) : ℕ :=
  if n % 4 = 0 then (2 + 3 * n) / 2
  else if n % 4 = 2 then n / 2
  else 2 + 3 * n

/-- Barker's conjectured recurrence a(n) = 2*a(n-4) - a(n-8) for `n > 7`. -/
theorem main : ∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * (a (n - 4) : ℤ) - (a (n - 8) : ℤ) := by
  sorry

end OMA.S_oeis_a324036
