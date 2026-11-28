import Mathlib

/-!
# A168222: a(n) = A006369(A006369(n))

Source: https://oeis.org/A168222
Credit: @jagong-cmu

Formalizes the conjectures of Colin Barker (Aug 15 2019) in OEIS A168222 (offset 0):
* G.f.: `x*(1 + 2*x + 3*x^2 + 7*x^3 + 9*x^4 + 5*x^5 + 6*x^6 + 15*x^7 + 4*x^8 + 15*x^9 +
  6*x^10 + 5*x^11 + 9*x^12 + 7*x^13 + 3*x^14 + 2*x^15 + x^16) /
  ((1 - x)^2*(1 + x + x^2)^2*(1 + x^3 + x^6)^2)`;
* `a(n) = 2*a(n-9) - a(n-18)` for `n > 17`.

Conventions:
* `A006369` is defined literally from its OEIS name: `a(n) = 2*n/3` for `n` divisible by 3,
  otherwise `a(n) = round(4*n/3)`. For `3 ∣ n` the division `2*n/3` on `ℕ` is exact. Otherwise
  `4*n/3` is computed in `ℚ`, rounded with `round` (never a tie here, since `4*n/3` has
  fractional part `1/3` or `2/3`), and the result, which is positive, is taken back to `ℕ` with
  `Int.toNat`.
* The offset is 0. The g.f. is stated in `PowerSeries ℤ` as an identity after the
  multiplication by the denominator, which is a unit (its constant term is 1).
* The recurrence is stated in `ℤ` for every `n >= 18`, so `n - 9` and `n - 18` are exact.
-/

namespace OMA.S_oeis_a168222

open PowerSeries

/-- A006369: `2*n/3` if `3 ∣ n`, otherwise `round(4*n/3)`. -/
def A006369 (n : ℕ) : ℕ :=
  if n % 3 = 0 then 2 * n / 3 else (round ((4 * n : ℚ) / 3)).toNat

/-- A168222: `a(n) = A006369(A006369(n))`. -/
def a (n : ℕ) : ℕ := A006369 (A006369 n)

/-- The g.f. conjecture and the recurrence `a(n) = 2*a(n-9) - a(n-18)` for `n > 17`. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2 * (1 + X ^ 3 + X ^ 6) ^ 2) =
      X * (1 + 2 * X + 3 * X ^ 2 + 7 * X ^ 3 + 9 * X ^ 4 + 5 * X ^ 5 + 6 * X ^ 6 +
        15 * X ^ 7 + 4 * X ^ 8 + 15 * X ^ 9 + 6 * X ^ 10 + 5 * X ^ 11 + 9 * X ^ 12 +
        7 * X ^ 13 + 3 * X ^ 14 + 2 * X ^ 15 + X ^ 16)) ∧
    ∀ n : ℕ, 18 ≤ n → (a n : ℤ) = 2 * (a (n - 9) : ℤ) - (a (n - 18) : ℤ) := by
  sorry

end OMA.S_oeis_a168222
