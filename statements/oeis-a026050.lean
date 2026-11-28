import Mathlib

/-!
# A026050: a(n) = (d(n)-r(n))/2, where d = A026049 and r is the periodic sequence with
fundamental period (1,0,0,1).

Source: https://oeis.org/A026050
Credit: @jagong-cmu

The entry gives the conjecture (R. J. Mathar, Jun 22 2013)
Conjecture: G.f. x^7*( 59-158*x+203*x^2-202*x^3+145*x^4-45*x^5 ) / ( (x^2+1)*(x-1)^4 ).

Definitions, as in the OEIS entries:
* A026049 (offset 7): `d(n) = dot_product(1,2,...,n)*(7,8,...,n,1,2,3,4,5,6)`. The second
  vector is `1,...,n` rotated left by 6 places: its `(i+1)`-th entry is `i + 7` if
  `i + 7 ≤ n`, else `i + 7 - n` (for `i = 0, ..., n-1`). The truncated subtraction
  `i + 7 - n` on `ℕ` is the usual one in the second case. The definition below is used only
  for `n ≥ 7`, the offset of the entry.
* `r` is the periodic sequence with fundamental period `(1,0,0,1)`, indexed from the first
  index `n = 7` of the entry: `r(7) = 1, r(8) = 0, r(9) = 0, r(10) = 1, r(11) = 1, ...`, so
  `r(n)` is entry `(n - 7) mod 4` of the list `(1,0,0,1)`. The data of the entry fix this
  phase (`a(7) = (119-1)/2 = 59`, `a(8) = 156/2 = 78`, `a(10) = (265-1)/2 = 132`).
* A026050 (offset 7): `a(n) = (d(n) - r(n))/2`. The difference `d(n) - r(n)` is even, so the
  floor division `/ 2` on `ℕ` is exact, and `r(n) ≤ 1 ≤ d(n)`, so the subtraction is exact.
* The generating function of a sequence with offset 7 is `Sum_{n>=7} a(n) x^n`. The series `A`
  below has coefficient `0` at `x^n` for `n < 7` and `a(n)` at `x^n` for `n ≥ 7`.
* The identity is stated in `ℤ[[x]]` with the denominator cleared:
  `A * ((x^2 + 1) * (x - 1)^4) = x^7 * (59 - 158x + 203x^2 - 202x^3 + 145x^4 - 45x^5)`.
  The denominator has constant coefficient `1`, a unit, so this form is equivalent to the
  quotient form.
-/

namespace OMA.S_oeis_a026050

open PowerSeries

/-- A026049: `d(n) = (1,2,...,n) . (7,8,...,n,1,2,3,4,5,6)`, for `n ≥ 7`. -/
def d (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (i + 1) * (if i + 7 ≤ n then i + 7 else i + 7 - n)

/-- The periodic sequence with fundamental period `(1,0,0,1)`, starting at `n = 7`. -/
def r (n : ℕ) : ℕ := if (n - 7) % 4 = 0 ∨ (n - 7) % 4 = 3 then 1 else 0

/-- A026050: `a(n) = (d(n) - r(n))/2`, for `n ≥ 7`. -/
def a (n : ℕ) : ℕ := (d n - r n) / 2

/-- The generating function `Sum_{n>=7} a(n) x^n`, with offset 7. -/
noncomputable def A : PowerSeries ℤ := mk fun n => if n < 7 then 0 else (a n : ℤ)

/-- The generating function of A026050 is
`x^7*(59-158*x+203*x^2-202*x^3+145*x^4-45*x^5)/((x^2+1)*(x-1)^4)`. -/
theorem main :
    A * ((X ^ 2 + 1) * (X - 1) ^ 4) =
      X ^ 7 * (59 - 158 * X + 203 * X ^ 2 - 202 * X ^ 3 + 145 * X ^ 4 - 45 * X ^ 5) := by
  sorry

end OMA.S_oeis_a026050
