import Mathlib

/-!
# A224670: Number of (n+1) X 3 0..2 matrices with each 2 X 2 subblock idempotent

Source: https://oeis.org/A224670
Credit: @xor2k
Sibling of OEIS A224671 (same conjecture wording); statement modelled on the accepted one for that entry.

Conjectures from Colin Barker, Feb 17 2018, as worded in the entry:
G.f.: x*(25 - 50*x + x^2 + 44*x^3 - 21*x^4) / ((1 - x)^3*(1 - x - x^2)).
a(n) = -2 + 2^(1-n)*sqrt(5)*(-(1-sqrt(5))^(1+n) + (1+sqrt(5))^(1+n)) + 2*(1+n) + (1+n)*(2+n)/2.
The entry also records the empirical recurrence
a(n) = 4*a(n-1) -5*a(n-2) +a(n-3) +2*a(n-4) -a(n-5), which is included as well.

Conventions:
* A matrix is a first row followed by `n` further rows; rows are maps `Fin 3 → Fin 3`. A `2 X 2`
  subblock consists of two consecutive rows and two consecutive columns (as in A224669 and
  A224671; this reproduces the data 25, 50, 76, ...). Its idempotence `A^2 = A` over the integers
  is spelled out as the four entry equations.
* Offset 1: `term n` for `n ≥ 1` is `a(n)`. The generating series has constant term 0, and the
  generating-function identity is multiplied by its denominator, whose constant term is 1.
* The closed form carries no range in the entry; it is stated in `ℝ` for every `n ≥ 1` (the whole
  offset range), with `2^(1-n)` an integer power `zpow` of `2`.
* The recurrence carries no range in the entry; it is stated for every `n` for which all indices
  `n-1, ..., n-5` lie in the offset range, i.e. `n > 5`.
-/

namespace OMA.S_oeis_a224670

/-- A row of the matrix: three entries in `0..2`. -/
abbrev Row := Fin 3 → Fin 3

/-- The entries of the matrix equation `A^2 = A` for `A = [[a, b], [c, d]]` over the integers. -/
def idempotent (a b c d : ℕ) : Bool :=
  decide (a*a+b*c=a ∧ a*b+b*d=b ∧ c*a+d*c=c ∧ c*b+d*d=d)

/-- Row `s` may follow row `r`: every `2 X 2` subblock formed by columns `j, j+1` of the two rows
is idempotent. -/
def compatible (r s : Row) : Bool :=
  decide (∀ j : Fin 2, idempotent (r j.castSucc) (r j.succ) (s j.castSucc) (s j.succ) = true)

/-- Number of ways to append `n` further rows below the row `r`. -/
def completions : ℕ → Row → ℕ
  | 0, _ => 1
  | n+1, r => ∑ s : Row, if compatible r s then completions n s else 0

/-- `A224670(n)`: the number of `(n+1) X 3` matrices with entries `0..2` and all `2 X 2`
subblocks idempotent. -/
def term (n : ℕ) : ℕ := ∑ r, completions n r

/-- The ordinary generating series `∑_{n ≥ 1} a(n) x^n` (offset 1, so the constant term is 0). -/
noncomputable def series : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then 0 else term n)

open PowerSeries in
theorem main :
    ((1 - X)^3 * (1 - X - X^2)) * series =
      X * (25 - 50*X + X^2 + 44*X^3 - 21*X^4) ∧
    (∀ n : ℕ, 0 < n → (term n : ℝ) =
      -2 + (2 : ℝ) ^ ((1 : ℤ) - n) * Real.sqrt 5 *
          (-(1 - Real.sqrt 5)^(1+n) + (1 + Real.sqrt 5)^(1+n)) +
        2 * (1 + n) + (1 + n) * (2 + n) / 2) ∧
    (∀ n : ℕ, 5 < n → (term n : ℤ) =
      4 * term (n-1) - 5 * term (n-2) + term (n-3) + 2 * term (n-4) - term (n-5)) := by
  sorry

end OMA.S_oeis_a224670
