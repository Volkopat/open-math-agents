import Mathlib

/-!
# A392976: Expansion of (1/x) * Series_Reversion( x * ((1-x^2)^2 - x) ).

Source: https://oeis.org/A392976
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A392976 (R. J. Mathar, Jan 29 2026):
Conjecture D-finite with recurrence 283*n*(n-1)*(n-2)*(83022305213*n -178385058984)*(n+1) *a(n)
-6*n*(n-1)*(n-2)*(12196786904129*n^2 -45110300936020*n +52641391340361)*a(n-1)
-6*(n-1)*(n-2)*(67790996421377*n^3 -248299346995054*n^2 +202497447227007*n +3061418504418)*a(n-2)
-2*(n-2)*(192167357944360*n^4 -559010679688491*n^3 -2120668219560541*n^2 +9123363136130610*n
-8342981628089220)*a(n-3) +5*(15640122296875*n^5 -565964885220500*n^4 +4989857715427325*n^3
-18667678380008380*n^2 +32085126156301848*n -20925325629575136)*a(n-4)
+10*(5*n-17)*(5*n-18) *(5*n-21)*(5*n-19)*(22509687685*n-60308240636)*a(n-5)=0.

Conventions:
* The sequence has offset 0 (data 1, 1, 4, 15, 67, 315, 1556, 7938, ...).
* `P` is the formal power series x * ((1-x^2)^2 - x) over `ℤ`.
* Series_Reversion(P) is the compositional inverse of P, i.e. the power series `R` with zero
  constant term and P(R(x)) = x. It is rendered by the Mathlib construction
  `PowerSeries.substInvOfIsUnit`, which needs a proof that the coefficient of x in P is a unit
  of `ℤ` (this coefficient is 1); that proof is the `by` block inside the definition of `R`.
* The factor 1/x shifts the coefficients by one: a(n) is the coefficient of x^(n+1) in `R`
  (the constant term of `R` is 0).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 5`, which is
  exactly the range in which all the indices n, n-1, ..., n-5 are at least the offset 0.
* The identity is stated in `ℤ`, with the natural number `n` cast to `ℤ`, so the subtractions
  and negative coefficients are exact.
-/

namespace OMA.S_oeis_a392976

/-- The power series x * ((1-x^2)^2 - x). -/
noncomputable def P : PowerSeries ℤ :=
  PowerSeries.X * ((1 - PowerSeries.X ^ 2) ^ 2 - PowerSeries.X)

/-- The series reversion (compositional inverse) of `P`. -/
noncomputable def R : PowerSeries ℤ :=
  PowerSeries.substInvOfIsUnit P (by
    have h : PowerSeries.coeff 1 P = 1 := by
      unfold P
      rw [PowerSeries.coeff_succ_X_mul]
      simp
    rw [h]
    exact isUnit_one)

/-- A392976 (offset 0): a(n) is the coefficient of x^n in (1/x) * Series_Reversion(P), that is
the coefficient of x^(n+1) in the reversion `R`. -/
noncomputable def a (n : ℕ) : ℤ := PowerSeries.coeff (n + 1) R

/-- For every `n ≥ 5`, the recurrence conjectured by R. J. Mathar holds. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    283 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (83022305213 * (n : ℤ) - 178385058984)
        * ((n : ℤ) + 1) * a n
      - 6 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2)
        * (12196786904129 * (n : ℤ) ^ 2 - 45110300936020 * (n : ℤ) + 52641391340361) * a (n - 1)
      - 6 * ((n : ℤ) - 1) * ((n : ℤ) - 2)
        * (67790996421377 * (n : ℤ) ^ 3 - 248299346995054 * (n : ℤ) ^ 2
          + 202497447227007 * (n : ℤ) + 3061418504418) * a (n - 2)
      - 2 * ((n : ℤ) - 2)
        * (192167357944360 * (n : ℤ) ^ 4 - 559010679688491 * (n : ℤ) ^ 3
          - 2120668219560541 * (n : ℤ) ^ 2 + 9123363136130610 * (n : ℤ) - 8342981628089220)
        * a (n - 3)
      + 5 * (15640122296875 * (n : ℤ) ^ 5 - 565964885220500 * (n : ℤ) ^ 4
          + 4989857715427325 * (n : ℤ) ^ 3 - 18667678380008380 * (n : ℤ) ^ 2
          + 32085126156301848 * (n : ℤ) - 20925325629575136) * a (n - 4)
      + 10 * (5 * (n : ℤ) - 17) * (5 * (n : ℤ) - 18) * (5 * (n : ℤ) - 21) * (5 * (n : ℤ) - 19)
        * (22509687685 * (n : ℤ) - 60308240636) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a392976
