import Mathlib

/-!
# A184878: Third column (negated) of triangle in A182971

Source: https://oeis.org/A184878
Credit: @jagong-cmu

Formalizes R. J. Mathar's OEIS A184878 conjecture (May 18 2026), offset 1:
`Conjectures: G.f.: x^5*(225+54*x+x^2)/(x-1)^10 .`
`a(n) = n *(n-1) *(n-2) *(n-3) *(n-4) *(n+2) *(n+1) *(35*n^2+182*n+240) /45360.`

Conventions:
* A182971 is the triangle of coefficients of `Q(n) = (x-n^2)*(x-(n-2)^2)*...*(x-(1 or 2)^2)`,
  highest powers first. Here `Q(n)` is the product over `0 <= i < floor((n+1)/2)` of
  `x - (n-2*i)^2` in `ℤ[x]`; it has degree `d = floor((n+1)/2)` (and `Q(0) = 1`).
* Row `n` of the triangle is `T(n,k) = [x^(d-k)] Q(n)` for `0 <= k <= d`. The columns are
  numbered from `k = 0` (the column of `1`s), and the third column is `k = 3`: this matches the
  OEIS data, e.g. `Q(5) = (x-1)(x-9)(x-25) = x^3 - 35x^2 + 259x - 225` and `a(5) = 225`.
  Where the row is too short (`k > d`) the entry is `0`, which gives the OEIS terms
  `a(1) = ... = a(4) = 0`.
* `a(n) = -T(n,3)` in `ℤ`. The closed form is stated in `ℚ` (so `n - 1`, ..., `n - 4` and the
  division by `45360` are the usual ones) for every `n >= 1` (the offset is 1).
* Why the closed form also states the g.f. conjecture. Since `(x - 1)^10 = (1 - x)^10` and
  `1/(1 - x)^10 = Sum_{m >= 0} binomial(m + 9, 9) x^m`, the coefficient of `x^n` in
  `x^5*(225 + 54*x + x^2)/(x - 1)^10` is
  `225*binomial(n + 4, 9) + 54*binomial(n + 3, 9) + binomial(n + 2, 9)`,
  with `binomial(m, 9) = 0` for `m < 9`. This vanishes for `n < 5`, as the closed form does.
  For `n >= 5` the three binomials have the common factor
  `(n + 2)(n + 1) n (n - 1)(n - 2)(n - 3)(n - 4)`, and the sum factors as
  `n(n-1)(n-2)(n-3)(n-4)(n+2)(n+1)(35n^2 + 182n + 240)/45360`, which is the polynomial in `main`.
  So the two conjectures are equivalent for `n >= 1`, and `main` states the closed form.
-/

namespace OMA.S_oeis_a184878

open Polynomial

/-- `Q(n) = (x-n^2)*(x-(n-2)^2)*...*(x-(1 or 2)^2)`. -/
noncomputable def Q (n : ℕ) : ℤ[X] :=
  ∏ i ∈ Finset.range ((n + 1) / 2), (X - C (((n - 2 * i : ℕ) : ℤ) ^ 2))

/-- Triangle A182971: `T(n,k)` is the coefficient of `x^(d-k)` in `Q(n)`, `d = deg Q(n)`. -/
noncomputable def T (n k : ℕ) : ℤ :=
  if k ≤ (n + 1) / 2 then (Q n).coeff ((n + 1) / 2 - k) else 0

/-- `a(n) = -T(n,3)`. -/
noncomputable def a (n : ℕ) : ℤ := -T n 3

/-- For every `n >= 1`:
`a(n) = n(n-1)(n-2)(n-3)(n-4)(n+2)(n+1)(35n^2+182n+240)/45360`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) = (n : ℚ) * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n + 2) * (n + 1) *
      (35 * n ^ 2 + 182 * n + 240) / 45360 := by
  sorry

end OMA.S_oeis_a184878
