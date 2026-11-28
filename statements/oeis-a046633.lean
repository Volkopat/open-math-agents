import Mathlib

/-!
# OEIS A046633: cubic residues modulo powers of 5

Source: https://oeis.org/A046633
Credit: @Heart-galaxy

The source has offset 0. Its independent closed formula, recorded by R. J. Mathar
on October 8, 2017, is 31*a(n)=5^(n+2)+2*b(n), where b has period 3 and values
3,15,13. That formula defines the sequence below; it is not the conjectured
recurrence. The source's Maple code confirms the three residue cases.

Mathar conjectured the order-four recurrence and generating function on
February 27, 2011. Charles R Greathouse IV confirmed them on January 3, 2013.
Both claims are retained. The generating function is expressed after multiplying
by its denominator, whose constant coefficient is one.
-/

namespace OMA.S_oeis_a046633

def b (n : ℕ) : ℕ := if n % 3 = 0 then 3 else if n % 3 = 1 then 15 else 13

/-- The independent explicit closed formula for the cubic-residue counting sequence. -/
def a (n : ℕ) : ℕ := (5 ^ (n + 2) + 2 * b n) / 31

noncomputable def generating : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))

noncomputable def denominator : PowerSeries ℚ :=
  (PowerSeries.X - 1) * (PowerSeries.C 5 * PowerSeries.X - 1) *
    (1 + PowerSeries.X + PowerSeries.X ^ 2)

noncomputable def numerator : PowerSeries ℚ :=
  1 - PowerSeries.C 4 * PowerSeries.X ^ 2 - PowerSeries.C 5 * PowerSeries.X ^ 3

/-- The conjectured recurrence and rational generating function. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) =
      5 * (a (n - 1) : ℤ) + (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ)) ∧
    denominator * generating = numerator := by
  sorry

end OMA.S_oeis_a046633
