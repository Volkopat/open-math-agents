import Mathlib

/-!
# A192031. Distances in helm graphs

Source: https://oeis.org/A192031
Credit: @physbuzz

Row r counts unordered pairs of vertices at each positive distance in the helm
graph with r spokes. We use the entry's independently stated Wiener polynomial
to define its row coefficients, as in its Maple program. Row 3 has three entries.
Each subsequent row has four. The sequence starts at index 3.

Colin Barker's conjectures of March 28, 2019 concern the generating function
and the recurrence of the flattened sequence. The denominator has constant term 1.
-/

namespace OMA.S_oeis_a192031

open PowerSeries

/-- The four coefficients of the helm graph Wiener polynomial, indexed from zero. -/
def row (r : ℚ) (j : ℕ) : ℚ :=
  match j with
  | 0 => 3*r
  | 1 => r*(r+3)/2
  | 2 => r*(r-2)
  | 3 => r*(r-3)/2
  | _ => 0

/-- Rows read in order, extended by zero below the offset. -/
def a (n : ℕ) : ℚ :=
  if n < 3 then 0 else if n < 6 then row 3 (n-3)
  else row (4 + ((n-6)/4 : ℕ)) ((n-6)%4)

theorem main :
    mk a * ((1-X)^3 * (1+X)^2 * (1+X^2)^3) =
      X^3 * (9 + 3*X^2 + 9*X^3 - 22*X^4 + 3*X^5 - 10*X^6 - 11*X^7 +
        16*X^8 + 2*X^9 + 6*X^10 + 3*X^11 - 3*X^12 - 3*X^13) ∧
    ∀ n : ℕ, 16 < n →
      a n = a (n-1) - a (n-2) + a (n-3) + 2*a (n-4) - 2*a (n-5) +
        2*a (n-6) - 2*a (n-7) - a (n-8) + a (n-9) - a (n-10) + a (n-11) := by
  sorry

end OMA.S_oeis_a192031
