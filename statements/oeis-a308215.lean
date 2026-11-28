import Mathlib

/-!
# A308215: multiplicative inverse of A001844(n+1) modulo A001844(n)

Source: https://oeis.org/A308215 (conjectures by Colin Barker, May 16 2019)

Entry (offset 0): a(n) is the multiplicative inverse of A001844(n+1) modulo A001844(n), where
A001844(n) = 2*n*(n+1) + 1 are the centered square numbers.
Formula section, Conjectures from Colin Barker, May 16 2019:
G.f.: x*(2 + 12*x + 5*x^2 + 3*x^3 + x^4 + x^5) / ((1 - x)^3*(1 + x)^3).
a(n) = (3 + (-1)^n + 2*(2+(-1)^n)*n + 2*(3+(-1)^n)*n^2) / 4 for n>0.
a(n) = 3*a(n-2) - 3*a(n-4) + a(n-6) for n>6.

Formalization notes:
* The inverse is taken in `ZMod (A001844 n)` and represented by its value in `[0, A001844 n)`,
  as the entry's PARI program `lift(1/Mod(f(n+1), f(n)))` does. Consecutive centered square
  numbers are coprime, so this is the inverse. For n = 0 the modulus is 1 and the value is 0,
  matching a(0) = 0 in the entry.
* The closed form is stated for n > 0 after multiplying both sides by 4, in the integers.
* The recurrence is stated in the integers. Since the denominator of the generating function
  has constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as
  A * D = N in the formal power series ring over the integers.
* Controls from the entry: a(0..6) = 0, 2, 12, 11, 39, 28, 82.
-/

namespace OMA.S_oeis_a308215

open PowerSeries

/-- A001844(n) = 2*n*(n+1) + 1, the centered square numbers. -/
def cs (n : ℕ) : ℕ := 2 * n * (n + 1) + 1

/-- A308215(n): the inverse of A001844(n+1) modulo A001844(n), as a residue in `[0, A001844(n))`. -/
def a (n : ℕ) : ℕ := (((cs (n + 1) : ℕ) : ZMod (cs n))⁻¹).val

/-- Barker's generating function, closed form and recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 3) =
      (X * (2 + 12 * X + 5 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5) : PowerSeries ℤ) ∧
    (∀ n : ℕ, 0 < n →
      4 * (a n : ℤ) = 3 + (-1) ^ n + 2 * (2 + (-1) ^ n) * n + 2 * (3 + (-1) ^ n) * n ^ 2) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6)) := by
  sorry

end OMA.S_oeis_a308215
