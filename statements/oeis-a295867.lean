import Mathlib

/-!
# A295867: Numbers of the form A000217(n)*A007494(n) that are divisible by 3.

Source: https://oeis.org/A295867
Credit: @ShoQo

Conjectures from Colin Barker, Feb 15 2018: "G.f.: 3*x*(3 + 7*x + 10*x^2 + 20*x^3 + 23*x^4 +
72*x^5 + 45*x^6 + 35*x^7 + 39*x^8 + 25*x^9 + 33*x^10 + 8*x^11 + 3*x^12 + x^13) / ((1 - x)^4*(1 + x
+ x^2 + x^3 + x^4)^3). a(n) = a(n-1) + 3*a(n-5) - 3*a(n-6) - 3*a(n-10) + 3*a(n-11) + a(n-15) -
a(n-16) for n>15." The entry adds: "Colin Barker's conjecture is true."

Formalization notes:
* A000217(n) = n(n+1)/2 (triangular numbers) and A007494(n) = n + ceiling(n/2) (the numbers
  congruent to 0 or 2 mod 3: 0, 2, 3, 5, 6, ...), both with offset 0.
* The terms are the multiples of 3 of the form A000217(n)*A007494(n), in increasing order, with
  offset 0 as in the entry (data: 0, 9, 30, 60, 120, 189, ...), so a(n) = `Nat.nth P n`.
* The recurrence is stated (over ℤ, as written); with the initial terms it is equivalent to the
  conjectured g.f., whose denominator (1-x)^4 (1+x+x^2+x^3+x^4)^3 = (1-x)(1-x^5)^3 has exactly
  these coefficients.
-/

namespace OMA.S_oeis_a295867

/-- A000217: triangular numbers. -/
def A000217 (n : ℕ) : ℕ := n * (n + 1) / 2

/-- A007494: numbers congruent to 0 or 2 mod 3, `n + ceiling(n/2)`. -/
def A007494 (n : ℕ) : ℕ := n + (n + 1) / 2

/-- Membership in A295867: multiples of 3 of the form A000217(n) * A007494(n). -/
def P (x : ℕ) : Prop := 3 ∣ x ∧ ∃ n, x = A000217 n * A007494 n

/-- A295867 (offset 0). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P n

theorem main : ∀ n : ℕ, 15 < n →
    (a n : ℤ) = a (n - 1) + 3 * a (n - 5) - 3 * a (n - 6) - 3 * a (n - 10) + 3 * a (n - 11)
      + a (n - 15) - a (n - 16) := by
  sorry

end OMA.S_oeis_a295867
