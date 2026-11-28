import Mathlib

/-!
# A274232: closed form and recurrence

Source: https://oeis.org/A274232
Credit: @ivillar

The number of partitions of 2^n into at most three parts, i.e. the coefficient of x^(2^n) in
1/((1-x)*(1-x^2)*(1-x^3)) (offset 0; data 1, 2, 4, 10, 30, 102, 374, 1430, ...). The entry
conjectures a(n) = (8 + 3*2^(1+n) + 4^n)/12 for n > 0 and a(n) = 7*a(n-1) - 14*a(n-2) + 8*a(n-3)
for n > 3.

Status: conjectures recorded in the entry.

Formalization notes:
* A partition of N into at most three parts is written N = a + b + c with a >= b >= c >= 0
  (padding with zero parts); it is determined by c in [0, floor(N/3)] and b in
  [c, floor((N - c)/2)], and `a` counts these pairs for N = 2^n.
* The closed form is stated multiplied out: 12 * a(n) = 8 + 3*2^(n+1) + 4^n. The recurrence is
  stated over ℤ.
* The conjectured generating function (1-5*x+4*x^2+2*x^3) / ((1-x)*(1-2*x)*(1-4*x)) is the rational
  function determined by the recurrence and the initial terms; it is not restated.
-/

namespace OMA.S_oeis_a274232

/-- A274232: the number of partitions `2^n = a + b + c` with `a ≥ b ≥ c ≥ 0`. -/
def a (n : ℕ) : ℕ :=
  ∑ c ∈ Finset.range (2 ^ n / 3 + 1), ∑ _b ∈ Finset.Icc c ((2 ^ n - c) / 2), 1

/-- The conjectured closed form (for `n > 0`) and recurrence (for `n > 3`) of A274232. -/
theorem main :
    (∀ n : ℕ, 0 < n → 12 * a n = 8 + 3 * 2 ^ (n + 1) + 4 ^ n) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a274232
