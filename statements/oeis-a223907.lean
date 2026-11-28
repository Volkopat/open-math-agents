import Mathlib

/-!
# A223907: Poly-Cauchy numbers of the second kind hat c_4^(-n).

Source: https://oeis.org/A223907
Credit: @jagong-cmu

The entry gives (Colin Barker, Mar 31 2013):
Conjecture: a(n) = 3*2^(1+n)+3*2^(1+2*n)+11*3^n+5^n. G.f.:
-2*x*(1440*x^3-1346*x^2+396*x-37) / ((2*x-1)*(3*x-1)*(4*x-1)*(5*x-1)).

Conventions:
* The entry says that the poly-Cauchy numbers of the second kind are
  hat c_n^(k) = (-1)^n * Sum_{m=0..n} |stirling1(n,m)| / (m+1)^k, with the unsigned Stirling
  numbers of the first kind (`Nat.stirlingFirst`). For the index `-k` with `k : ℕ` the term
  `1 / (m+1)^(-k)` is `(m+1)^k`, so `hatc n k` below is hat c_n^(-k), an integer.
* `a n = hatc 4 n` is hat c_4^(-n). Offset 1, as in the entry (data: 74, 244, 854, 3148, ...).
* The closed form is stated for every `n >= 1`.
* The generating function of a sequence with offset 1 is `Sum_{n>=1} a(n) x^n`. The series
  `A` below has coefficient `0` at `x^0` and coefficient `a(n)` at `x^n` for `n >= 1`.
  The g.f. is stated as an identity of formal power series over `ℤ`, with the denominator
  cleared. The denominator has constant coefficient `1`, so it is a unit in `ℤ[[x]]`, and this
  form is equivalent to the quotient form.
-/

namespace OMA.S_oeis_a223907

open PowerSeries

/-- Poly-Cauchy number of the second kind hat c_n^(-k) =
`(-1)^n * Sum_{m=0..n} |s(n,m)| * (m+1)^k`. -/
def hatc (n k : ℕ) : ℤ :=
  (-1) ^ n * ∑ m ∈ Finset.range (n + 1), (Nat.stirlingFirst n m : ℤ) * ((m : ℤ) + 1) ^ k

/-- A223907: `a(n) = hat c_4^(-n)`. -/
def a (n : ℕ) : ℤ := hatc 4 n

/-- The generating function `Sum_{n>=1} a(n) x^n` of the sequence, with offset 1. -/
noncomputable def A : PowerSeries ℤ := mk fun n => if n = 0 then 0 else a n

/-- Closed form and generating function of A223907. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 3 * 2 ^ (1 + n) + 3 * 2 ^ (1 + 2 * n) + 11 * 3 ^ n + 5 ^ n) ∧
      A * ((2 * X - 1) * (3 * X - 1) * (4 * X - 1) * (5 * X - 1)) =
        -2 * X * (1440 * X ^ 3 - 1346 * X ^ 2 + 396 * X - 37) := by
  sorry

end OMA.S_oeis_a223907
