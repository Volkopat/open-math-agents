import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Nat.Factorial.Basic

/-!
# A001518: a generating-function identity for Bessel polynomials at three

The conjecture is Peter Bala's December 2025 formula in OEIS A001518.
The Bessel values use the recurrence listed in that entry. The right-hand
coefficients use the product defining the sextuple factorials in A011781.
The denominator is a formal power series with constant coefficient one.

Sources: https://oeis.org/A001518 and https://oeis.org/A011781
-/

namespace OMA.S_oeis_a001518

open Finset PowerSeries

def besselAtThree : ℕ → ℚ
  | 0 => 1
  | 1 => 4
  | n + 2 => 3 * (2 * (n : ℚ) + 3) * besselAtThree (n + 1) + besselAtThree n

def sextupleFactorial (n : ℕ) : ℚ :=
  ∏ k ∈ range n, (6 * (k : ℚ) + 3)

theorem main :
    (mk fun n => besselAtThree n / (n.factorial : ℚ)) *
        (1 + X * mk (fun n => besselAtThree n / ((n + 1).factorial : ℚ)))⁻¹ =
      mk (fun n => sextupleFactorial n / (n.factorial : ℚ)) := by
  sorry

end OMA.S_oeis_a001518
