import Mathlib

/-!
# OEIS A308217: Barker's conjectures for the inverse of A001844(n) modulo A001844(n+1)

Source: https://oeis.org/A308217 (Colin Barker, May 16 2019)

Entry A308217, offset 0: a(n) is the multiplicative inverse of A001844(n) modulo A001844(n+1);
where A001844 is the sequence of centered square numbers.
Formula section, conjectures from Colin Barker, May 16 2019:
G.f.: (1 + 8*x - x^2 - x^3 + x^5) / ((1 - x)^3*(1 + x)^3).
a(n) = 3*a(n-2) - 3*a(n-4) + a(n-6) for n>5.
a(n) = (9 - 5*(-1)^n + (8-6*(-1)^n)*n - 2*(-1+(-1)^n)*n^2) / 4.

Formalization notes:
* A001844(n) = 2n(n+1) + 1. The inverse is taken in ZMod (A001844(n+1)) and read back as its
  residue in 0..A001844(n+1)-1 (consecutive centered squares are coprime, so the inverse exists);
  this is the entry's PARI program lift(1/Mod(f(n), f(n+1))).
* The statement is the conjunction of the three conjectures. Since the denominator of the
  generating function has constant term 1, the identity A(x) = N/D for
  A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal power series ring over the
  integers. The recurrence is stated in the integers. The closed form, which has no stated range,
  is stated for every n >= 0 after multiplying both sides by 4, in the integers.
* Controls from the entry: the definition gives 1, 8, 2, 23, 3, 46, 4, 77 for n = 0..7.
-/

namespace OMA.S_oeis_a308217

open PowerSeries

/-- A001844(n) = 2n(n+1) + 1, the centered square numbers. -/
def c (n : ℕ) : ℕ := 2 * n * (n + 1) + 1

/-- A308217(n): the multiplicative inverse of A001844(n) modulo A001844(n+1), as a residue in
0..A001844(n+1)-1. -/
def a (n : ℕ) : ℕ := ((c n : ZMod (c (n + 1)))⁻¹).val

/-- Barker's generating function, recurrence and closed form. -/
theorem main :
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 3) =
      (1 + 8 * X - X ^ 2 - X ^ 3 + X ^ 5 : PowerSeries ℤ) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6)) ∧
    (∀ n : ℕ, 4 * (a n : ℤ) =
      9 - 5 * (-1) ^ n + (8 - 6 * (-1) ^ n) * n - 2 * (-1 + (-1) ^ n) * n ^ 2) := by
  sorry

end OMA.S_oeis_a308217
