import Mathlib

/-!
# A094047: Mathar's recurrence, corrected to n ≥ 6

Source: https://oeis.org/A094047
Credit: @ivillar

Status: corrected recurrence (n ≥ 6): fails as stated at n = 5 (the left side is 6 at n = 5 on the
OEIS data). The entry records the recurrence as a conjecture; no proof or verification is noted there.
`main` is the corrected recurrence (n ≥ 6), which is proved from the recurrence given in the entry by
Seiichi Manyama.

A094047 (offset 1): number of seating arrangements of n couples around a round table (up to rotations)
so that each person sits between two people of the opposite sex and no couple is seated together;
data 0, 0, 2, 12, 312, 9600, 416880, 23879520, 1749363840, 159591720960, ...

Conjecture (R. J. Mathar, Nov 02 2015):
a(n) +(-n^2+2*n-3)*a(n-1) -(n-2)*(n^2-3*n+5)*a(n-2) -3*(n-2)*(n-3)*a(n-3) +(n-2)*(n-3)*(n-4)*a(n-4) = 0.
(This is the first of the two recurrences conjectured in the entry on that date.)

Formalization: the entry gives the recurrence
a(n) = (n-1) * (n * (a(n-1) + a(n-2)) - 4 * (-1)^n * (n-3)!) for n > 3 (Seiichi Manyama, Jan 18 2020),
and this recurrence is used as the definition here, together with the listed initial terms
a(1) = 0, a(2) = 0, a(3) = 2. `main` is stated for every a : ℕ → ℚ with these initial values and this
recurrence for n ≥ 4; these conditions determine a(n) for all n ≥ 1. The sequence has offset 1 and the
conjectured recurrence involves a(n-4), so as stated it starts at n = 5, where it fails on the data:
(1)*(312) + (-18)*(12) + (-45)*(2) + (-18)*(0) + (6)*(0) = 6. It vanishes from n = 6 on, for example at
n = 6: (1)*(9600) + (-27)*(312) + (-92)*(12) + (-36)*(2) + (24)*(0) = 0.
-/

namespace OMA.S_oeis_a094047

/-- The corrected recurrence (n ≥ 6): Mathar's recurrence, which fails at n = 5. -/
theorem main : ∀ a : ℕ → ℚ, a 1 = 0 →
    a 2 = 0 →
    a 3 = 2 →
    (∀ n : ℕ, 4 ≤ n → a n = ((n : ℚ) - 1) *
      ((n : ℚ) * (a (n - 1) + a (n - 2)) - 4 * (-1 : ℚ) ^ n * ((n - 3).factorial : ℚ))) →
    ∀ n : ℕ, 6 ≤ n →
      a n + (-(n : ℚ) ^ 2 + 2 * (n : ℚ) - 3) * a (n - 1) -
        ((n : ℚ) - 2) * ((n : ℚ) ^ 2 - 3 * (n : ℚ) + 5) * a (n - 2) -
        3 * ((n : ℚ) - 2) * ((n : ℚ) - 3) * a (n - 3) +
        ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a094047
