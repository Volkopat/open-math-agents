import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Rat.Defs

/-!
# A recurrence for products of Catalan and Motzkin numbers

N. J. A. Sloane's sequence has offset 1 and term `C(n) * M(n-1)`.
The Motzkin numbers are specified over the rationals by their standard
recurrence and initial values, as in OEIS A001006. The middle term of
R. J. Mathar's August 2017 conjecture is printed with the factor `-2*-n`.
The displayed subtraction followed by a negative index factor is retained.

Sources: https://oeis.org/A290443 and https://oeis.org/A001006.
Formalization by @anmolspace.
-/

namespace OMA.S_oeis_a290443

/-- The Motzkin numbers, with the offset and recurrence of A001006. -/
def motzkin : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | k+2 => ((2*(k : ℚ)+5) * motzkin (k+1) + 3*((k : ℚ)+1) * motzkin k) / (k+4 : ℚ)

/-- Sequence A290443, used at indices `n ≥ 1`. -/
def a (n : ℕ) : ℚ := (catalan n : ℚ) * motzkin (n-1)

theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℚ)*((n : ℚ)+1)^2*a n - 2*(-(n : ℚ))*(2*(n : ℚ)-1)^2*a (n-1)
      - 12*((n : ℚ)-2)*(2*(n : ℚ)-1)*(2*(n : ℚ)-3)*a (n-2) = 0 := by
  sorry

end OMA.S_oeis_a290443
