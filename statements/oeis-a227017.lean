import Mathlib.Data.Rat.Defs

/-!
# Three formulas for OEIS A227017

The sequence is indexed from 1 and is the floor of the harmonic mean over
successive pentagonal blocks. The closed form below uses exactly the printed
index. The recurrence is printed for n > 1. Requiring all four referenced
terms to be in the sequence's declared domain gives n ≥ 5.

The numerator and denominator of the printed generating function both have
constant term -1. After changing both signs, the proposed numerator is
1 + x + 2x² + 3x³ - x⁴ and the denominator is 1 - 2x + 2x³ - x⁴.
We state their formal power series identity coefficientwise, starting with
a(1) at degree zero as indicated by the constant term.

Source: https://oeis.org/A227017
Credit: @ali-hamdan-007
-/

namespace OMA.S_oeis_a227017

def pentagonal (n : ℕ) : ℕ := n * (3 * n - 1) / 2

def a (n : ℕ) : ℤ :=
  let before := pentagonal (n - 1)
  let count := pentagonal n - before
  let reciprocals := (List.range count).map fun i =>
    (1 : ℚ) / ((before + i + 1 : ℕ) : ℚ)
  ((count : ℚ) / reciprocals.sum).floor

/-- The coefficient of degree k in the series starting with a(1). -/
def seriesCoeff (k : ℤ) : ℤ := if k < 0 then 0 else a (k.toNat + 1)

def numeratorCoeff : ℕ → ℤ
  | 0 | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => -1
  | _ => 0

theorem main :
    (∀ n : ℕ, 1 ≤ n →
      4 * a n = 1 - (-1 : ℤ)^n + 4 * (n : ℤ) + 6 * (n : ℤ)^2) ∧
    (∀ n : ℕ, 5 ≤ n →
      a n = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4)) ∧
    (∀ n : ℕ, seriesCoeff n - 2 * seriesCoeff ((n : ℤ) - 1)
      + 2 * seriesCoeff ((n : ℤ) - 3) - seriesCoeff ((n : ℤ) - 4)
      = numeratorCoeff n) := by
  sorry

end OMA.S_oeis_a227017
