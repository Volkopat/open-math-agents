import Mathlib

/-!
# A224671: Number of (n+1) X 4 0..2 matrices with each 2 X 2 subblock idempotent

Source: https://oeis.org/A224671
Credit: @xor2k
Sibling of OEIS A224669 (same conjecture wording); statement modelled on the accepted one for that entry.

Conjectures from Colin Barker, Feb 17 2018, as worded in the entry:
G.f.: x*(41 - 88*x + 9*x^2 + 77*x^3 - 41*x^4 + x^5) / ((1 - x)^3*(1 - x - x^2)).
a(n) = 5 + (2^(-1-n)*((1-sqrt(5))^n*(-19+29*sqrt(5)) + (1+sqrt(5))^n*(19+29*sqrt(5)))) / sqrt(5)
  + 4*(1+n) + (1+n)*(2+n)/2 for n>1.
The entry also records the empirical recurrence
a(n) = 4*a(n-1) -5*a(n-2) +a(n-3) +2*a(n-4) -a(n-5) for n>6, which is included as well.

Conventions:
* A matrix is a first row followed by `n` further rows; rows are maps `Fin 4 → Fin 3`. A `2 X 2`
  subblock consists of two consecutive rows and two consecutive columns (as in A224669; this
  reproduces the data 41, 76, 108, ...). Its idempotence `A^2 = A` over the integers is spelled out
  as the four entry equations.
* Offset 1: `term n` for `n ≥ 1` is `a(n)`. The generating series has constant term 0, and the
  generating-function identity is multiplied by its denominator, whose constant term is 1.
* The closed form is stated in `ℝ` for `n > 1`, with `2^(-1-n) / sqrt 5` written as
  `1 / (2^(n+1) * sqrt 5)`.
-/

namespace OMA.S_oeis_a224671

/-- A row of the matrix: four entries in `0..2`. -/
abbrev Row := Fin 4 → Fin 3

/-- The entries of the matrix equation `A^2 = A` for `A = [[a, b], [c, d]]` over the integers. -/
def idempotent (a b c d : ℕ) : Bool :=
  decide (a*a+b*c=a ∧ a*b+b*d=b ∧ c*a+d*c=c ∧ c*b+d*d=d)

/-- Row `s` may follow row `r`: every `2 X 2` subblock formed by columns `j, j+1` of the two rows
is idempotent. -/
def compatible (r s : Row) : Bool :=
  decide (∀ j : Fin 3, idempotent (r j.castSucc) (r j.succ) (s j.castSucc) (s j.succ) = true)

/-- Number of ways to append `n` further rows below the row `r`. -/
def completions : ℕ → Row → ℕ
  | 0, _ => 1
  | n+1, r => ∑ s : Row, if compatible r s then completions n s else 0

/-- `A224671(n)`: the number of `(n+1) X 4` matrices with entries `0..2` and all `2 X 2`
subblocks idempotent. -/
def term (n : ℕ) : ℕ := ∑ r, completions n r

/-- The ordinary generating series `∑_{n ≥ 1} a(n) x^n` (offset 1, so the constant term is 0). -/
noncomputable def series : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then 0 else term n)

open PowerSeries in
theorem main :
    ((1 - X)^3 * (1 - X - X^2)) * series =
      X * (41 - 88*X + 9*X^2 + 77*X^3 - 41*X^4 + X^5) ∧
    (∀ n : ℕ, 1 < n → (term n : ℝ) =
      5 + ((1 - Real.sqrt 5)^n * (-19 + 29 * Real.sqrt 5) +
          (1 + Real.sqrt 5)^n * (19 + 29 * Real.sqrt 5)) / (2^(n+1) * Real.sqrt 5) +
        4 * (1 + n) + (1 + n) * (2 + n) / 2) ∧
    (∀ n : ℕ, 6 < n → (term n : ℤ) =
      4 * term (n-1) - 5 * term (n-2) + term (n-3) + 2 * term (n-4) - term (n-5)) := by
  sorry

end OMA.S_oeis_a224671
