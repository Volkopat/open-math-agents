import Mathlib.Data.Rat.Defs

/-!
# Three formulas for OEIS A227013

The entry begins at n = 1. Its nth block consists of the integers from
(n−1)⁴ + 1 through n⁴, inclusive.

The proposed closed form uses its printed index. For integral n the only
values of 2 cos(2πn/3) are 2 for n ≡ 0 mod 3 and −1 for n ≡ 1, 2 mod 3.
Replacing that factor by its exact rational value avoids real arithmetic.

The recurrence is printed for n > 2. The last term a(n−7) belongs to the
sequence starting at 1 precisely when n ≥ 8. The generating function has
constant coefficient 1 = a(1). We give the identity coefficientwise after
multiplying by (1−x)⁵(1+x+x²) and changing the sign of the printed numerator.

Source: https://oeis.org/A227013
Credit: @ali-hamdan-007
-/

namespace OMA.S_oeis_a227013

/-- Floor of the harmonic mean over the nth fourth-power block. -/
def a (n : ℕ) : ℤ :=
  let before := (n - 1)^4
  let count := n^4 - before
  let reciprocals := (List.range count).map fun i =>
    (1 : ℚ) / ((before + i + 1 : ℕ) : ℚ)
  ((count : ℚ) / reciprocals.sum).floor

def proposed (n : ℕ) : ℚ :=
  let x : ℚ := n
  let twiceCos : ℚ := if n % 3 = 0 then 2 else -1
  47/9 + 14*x + 41*x^2/3 + 6*x^3 + x^4 - twiceCos/9

/-- Coefficient of degree k in the series beginning with the term a(1). -/
def seriesCoeff (k : ℤ) : ℤ := if k < 0 then 0 else a (k.toNat + 1)

def numeratorCoeff : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 22
  | 3 => 23
  | 4 => 20
  | 5 => 4
  | 6 => -2
  | 7 => 3
  | 8 => -1
  | _ => 0

theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = proposed n) ∧
    (∀ n : ℕ, 8 ≤ n →
      a n = 4*a (n-1) - 6*a (n-2) + 5*a (n-3) - 5*a (n-4)
        + 6*a (n-5) - 4*a (n-6) + a (n-7)) ∧
    (∀ n : ℕ, seriesCoeff n - 4*seriesCoeff ((n : ℤ)-1)
      + 6*seriesCoeff ((n : ℤ)-2) - 5*seriesCoeff ((n : ℤ)-3)
      + 5*seriesCoeff ((n : ℤ)-4) - 6*seriesCoeff ((n : ℤ)-5)
      + 4*seriesCoeff ((n : ℤ)-6) - seriesCoeff ((n : ℤ)-7) = numeratorCoeff n) := by
  sorry

end OMA.S_oeis_a227013
