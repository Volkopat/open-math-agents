import Mathlib

/-!
# A262242: Triangular numbers representable as 2^x + 2^y.

Source: https://oeis.org/A262242
Credit: @rtflynn

Colin Barker (Sep 16 2015), in the formula section of A262242:
  Conjectures: a(n) = 2^(n-5)*(2^n+4) for n>5. a(n) = 6*a(n-1)-8*a(n-2) for n>7.
  G.f.: x*(240*x^6+28*x^5-70*x^4+24*x^3-2*x^2-12*x+3) / ((2*x-1)*(4*x-1)).

Conventions:
* Triangular numbers are k(k+1)/2 with k ≥ 0, and x, y range over all naturals (x = y is
  allowed; it adds no term, since no power of 2 other than 1 is triangular, and 1 is not a sum of
  two powers of 2). The terms are listed in increasing order, offset 1:
  a(n) is `Nat.nth S (n - 1)`, the (n-1)-th element of the set S counted from 0.
* The g.f. is stated for the series with constant term 0 and coefficient a(n) at X^n for n ≥ 1,
  as an identity of formal power series over ℚ, (∑ a(n) X^n) * (2X - 1)(4X - 1) = numerator.
* The closed form is stated in ℕ for n ≥ 6 (n > 5), the recurrence in ℤ for n ≥ 8 (n > 7).

Numerical check: the elements of S below 10^7 are 3, 6, 10, 36, 66, 136, 528, 2080, 8256,
32896, 131328, 524800, 2098176, 8390656, the DATA of the entry.
-/

namespace OMA.S_oeis_a262242

/-- Triangular numbers that are a sum of two powers of 2. -/
def S : Set ℕ := {t | (∃ k : ℕ, t = k * (k + 1) / 2) ∧ ∃ x y : ℕ, t = 2 ^ x + 2 ^ y}

/-- A262242 (offset 1): the n-th element of S in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (· ∈ S) (n - 1)

/-- Barker's conjectures: the closed form for n > 5, the recurrence for n > 7 and the g.f. -/
theorem main : (∀ n : ℕ, 6 ≤ n → a n = 2 ^ (n - 5) * (2 ^ n + 4)) ∧
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 8 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((2 * PowerSeries.X - 1) * (4 * PowerSeries.X - 1)) =
      PowerSeries.X * (240 * PowerSeries.X ^ 6 + 28 * PowerSeries.X ^ 5 - 70 * PowerSeries.X ^ 4 +
        24 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 2 - 12 * PowerSeries.X + 3) := by
  sorry

end OMA.S_oeis_a262242
