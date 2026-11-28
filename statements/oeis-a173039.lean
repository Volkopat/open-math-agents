import Mathlib

/-!
# A173039: Odd numerators of the fractions (1/4-1/n^2), n >= -2.

Source: https://oeis.org/A173039
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 1, data -3, -1, -3, 5, 3, 21, 45, 15, 77, 117, 35, 165, 221, 63, ...)
records in its FORMULA section:

  Conjecture: a(n)= +3*a(n-3) -3*a(n-6) +a(n-9). G.f.: ( 3+x+3*x^2-14*x^3-6*x^4-30*x^5-21*x^6
  -3*x^7-5*x^8 ) / ( (x-1)^3*(1+x+x^2)^3 ). - R. J. Mathar, Dec 02 2010

Conventions:
* `num n` is the numerator (in lowest terms, sign carried by the numerator) of the rational number
  `1/4 - 1/n^2` for an integer `n ≠ 0`. As stated in the entry's COMMENTS (the sequence is the odd
  numbers of A061037 extended to negative `n`, using `-1` to represent `-1/0` at `n = 0`), we set
  `num 0 = -1`.
* The sequence lists, in order of increasing `n = -2, -1, 0, 1, 2, ...`, those values `num n` that are
  odd. We index the candidates by `m : ℕ` with `n = m - 2`; `IsOddNum m` says that `num (m - 2)` is
  odd, and `Nat.nth IsOddNum j` is the `j`-th such `m` (counting from `j = 0`).
* The sequence is indexed from `1` as in the entry: `a k = num (Nat.nth IsOddNum (k - 1) - 2)` for
  `k ≥ 1` (so `a 1 = num (-1) = -3`, `a 2 = num 0 = -1`, `a 3 = num 1 = -3`, `a 4 = num 3 = 5`); the
  value `a 0` plays no role.
* The recurrence is claimed for every `n` for which all its terms are defined, that is `n ≥ 10`.
* The g.f. is read with the constant term corresponding to `a(1)`, i.e. as the power series
  `Sum_{k >= 0} a(k+1) x^k` (this is the reading that matches the data); multiplying out the
  denominator, the claim is that this series times `(x-1)^3*(1+x+x^2)^3` equals the numerator
  polynomial.
-/

namespace OMA.S_oeis_a173039

open PowerSeries

/-- The numerator of `1/4 - 1/n^2` (A061037 extended to integer `n`), with the convention
`num 0 = -1` from the entry. -/
def num (n : ℤ) : ℤ :=
  if n = 0 then -1 else ((1 / 4 : ℚ) - 1 / (n : ℚ) ^ 2).num

/-- The candidate with index `m` (that is, `n = m - 2 ≥ -2`) has an odd numerator. -/
def IsOddNum (m : ℕ) : Prop := Odd (num ((m : ℤ) - 2))

/-- A173039, indexed from `1`: the `k`-th odd value of `num n` for `n = -2, -1, 0, 1, ...`. -/
noncomputable def a (k : ℕ) : ℤ := num ((Nat.nth IsOddNum (k - 1) : ℤ) - 2)

/-- Mathar's conjecture for A173039: the order-9 recurrence and the rational generating function. -/
theorem main :
    (∀ n : ℕ, 10 ≤ n → a n = 3 * a (n - 3) - 3 * a (n - 6) + a (n - 9)) ∧
    PowerSeries.mk (fun k => a (k + 1)) * ((X - 1) ^ 3 * (1 + X + X ^ 2) ^ 3) =
      (3 + X + 3 * X ^ 2 - 14 * X ^ 3 - 6 * X ^ 4 - 30 * X ^ 5 - 21 * X ^ 6 - 3 * X ^ 7
        - 5 * X ^ 8 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a173039
