import Mathlib

/-!
# A162171: Third column of A162170.

Source: https://oeis.org/A162171
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

## The conjecture

OEIS A162171 (Mats Granvik, Jun 27 2009), offset 1, FORMULA line:

> a(n) = n*(n+1)/2 * A000111(n-1) (conjectured). - Mike Tryczak, Jun 17 2015

followed by

> The above conjecture by Tryczak is correct. With an offset of 2, the e.g.f. is
> x^2/2!*(sec(x) + tan(x)). - Peter Bala, Sep 08 2021

So the statement is known (Peter Bala, 2021, in the entry itself).

## Modelling choices

* `A162169 n k` (OEIS offset 1, rows `n ≥ 1`, columns `1 ≤ k ≤ n`) is the signed Pascal
  triangle, given by the explicit formula in the A162169 entry (Mike Tryczak, Jun 17 2015;
  also Mats Granvik's Mathematica program there): for odd columns `k`,
  `T(n, k) = binomial(n-1, k-1) * (-1)^floor((n+k-1)/2)`; for even columns, `T(n, k) = 1`
  if `n = k` and `0` otherwise. These are exactly the coefficients `n! [x^n t^(k-1)]` of the
  e.g.f. `(cos x - sin x) * cosh(t x) + sinh(t x)` named in A162169. The formula reproduces
  the whole DATA line of A162169. For `k > n` it gives `0`.
* `A162170` is the matrix inverse of the infinite lower unitriangular matrix `A162169`.
  Its rows `1..n` are the rows of the inverse of the `n × n` truncation, so
  `A162170 n k` is defined as entry `(n, k)` of the inverse (over `ℚ`) of the `n × n`
  matrix `(A162169 i j)_{1 ≤ i, j ≤ n}` (1-based indices shifted to `Fin n`).
  This reproduces the DATA line of A162170.
* `a n = A162170 (n + 2) 3`: the third column of A162170 starts in row 3, and A162171 has
  offset 1, so `a 1 = A162170 3 3 = 1`, `a 2 = A162170 4 3 = 3`, ... (matches the DATA
  line `1, 3, 6, 20, 75, 336, ...`).
* `A000111 n` (Euler up/down numbers) is defined by its e.g.f. `sec x + tan x`, the name of
  A000111: `A000111 n = n! * [x^n] (sec x + tan x)` in `PowerSeries ℚ`, with
  `sec = cos⁻¹` and `tan = sin * cos⁻¹` (the constant coefficient of `cos` is `1`).
* The conjecture is stated in `ℚ` for every `n ≥ 1` (the offset of A162171), with
  `n*(n+1)/2` computed in `ℚ` (it is an integer anyway).
* Bala's e.g.f. remark is the same identity rewritten as a generating function, so it is
  not stated separately.
-/

namespace OMA.S_oeis_a162171

/-- A162169 (offset 1): for odd `k`, `binomial(n-1, k-1) * (-1)^floor((n+k-1)/2)`;
for even `k`, `1` on the diagonal and `0` elsewhere. -/
def A162169 (n k : ℕ) : ℤ :=
  if k % 2 = 1 then ((n - 1).choose (k - 1) : ℤ) * (-1) ^ ((n + k - 1) / 2)
  else if n = k then 1 else 0

/-- The `n × n` truncation of A162169 (rows and columns `1..n`), over `ℚ`. -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (A162169 (i.val + 1) (j.val + 1) : ℚ)

/-- A162170 (offset 1): the matrix inverse of A162169; row `n` is read from the inverse
of the `n × n` truncation. -/
noncomputable def A162170 (n k : ℕ) : ℚ :=
  if h : 1 ≤ k ∧ k ≤ n then
    (M n)⁻¹ ⟨n - 1, by omega⟩ ⟨k - 1, by omega⟩
  else 0

/-- A162171 (offset 1): the third column of A162170, `a n = A162170 (n + 2) 3`. -/
noncomputable def a (n : ℕ) : ℚ := A162170 (n + 2) 3

/-- A000111: Euler (up/down) numbers, `n! [x^n] (sec x + tan x)`. -/
noncomputable def A000111 (n : ℕ) : ℚ :=
  (n.factorial : ℚ) *
    PowerSeries.coeff n ((PowerSeries.cos ℚ)⁻¹ + PowerSeries.sin ℚ * (PowerSeries.cos ℚ)⁻¹)

/-- Mike Tryczak's conjecture (Jun 17 2015), proved by Peter Bala (Sep 08 2021):
`a(n) = n*(n+1)/2 * A000111(n-1)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = (n : ℚ) * ((n : ℚ) + 1) / 2 * A000111 (n - 1) := by
  sorry

end OMA.S_oeis_a162171
