import Mathlib

/-!
# A128957: Barker's recurrence and g.f. for a count of integers up to 10^n

Source: https://oeis.org/A128957
Credit: @ivillar

A128957 (offset 2): a(n) is the number of positive integers m ≤ 10^n such that m is not divisible
by at least one of the primes 2, 5 and is not divisible by at least one of the primes 3, 7;
data 86, 857, 8571, 85715, 857142, ...
Conjectures (Colin Barker, Nov 06 2017):
G.f.: x^2*(86 + 83*x + 84*x^2 + 89*x^3 + 81*x^4 + 90*x^5) / ((1 + x)*(1 - 10*x)*(1 - x + x^2)*(1 + x + x^2));
a(n) = 9*a(n-1) + 9*a(n-2) + 9*a(n-3) + 9*a(n-4) + 9*a(n-5) + 10*a(n-6) for n > 7.

Formalization notes.
* a(n) counts m in [1, 10^n] with (2 ∤ m or 5 ∤ m) and (3 ∤ m or 7 ∤ m). The terms are cast to ℤ.
* The g.f. of the offset-2 sequence is Sum_{n >= 2} a(n) x^n, written as `PowerSeries.mk` of the
  function that is 0 for n < 2 and a(n) for n ≥ 2; the identity is stated over ℤ⟦X⟧,
  cross-multiplied by the denominator, whose constant coefficient is 1.
-/

namespace OMA.S_oeis_a128957

open PowerSeries

/-- A128957: the number of m in [1, 10^n] not divisible by both 2 and 5, nor by both 3 and 7. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (10 ^ n)).filter (fun m => (¬ 2 ∣ m ∨ ¬ 5 ∣ m) ∧ (¬ 3 ∣ m ∨ ¬ 7 ∣ m))).card

/-- Barker's conjectures: the recurrence for n > 7, and the g.f. (cross-multiplied). -/
theorem main :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 9 * a (n - 1) + 9 * a (n - 2) + 9 * a (n - 3) + 9 * a (n - 4) +
      9 * a (n - 5) + 10 * a (n - 6)) ∧
    PowerSeries.mk (fun n => if n < 2 then 0 else (a n : ℤ)) *
        ((1 + X) * (1 - 10 * X) * (1 - X + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℤ) =
      X ^ 2 * (86 + 83 * X + 84 * X ^ 2 + 89 * X ^ 3 + 81 * X ^ 4 + 90 * X ^ 5) := by
  sorry

end OMA.S_oeis_a128957
