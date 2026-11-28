import Mathlib

/-!
# A121639: Mathar's recurrence, corrected to n ≥ 7

Source: https://oeis.org/A121639
Credit: @ivillar

Status: false as stated at n = 6 (the left side is 1 at n = 6 on the OEIS data); `main` is the
corrected recurrence (n ≥ 7), which is proved. It follows from the recurrence with factorials
recorded in the entry, which is used as the definition here.

A121639 (offset 1): number of 2-cell columns in all deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column;
data 0, 1, 5, 25, 147, 996, 7668, 66264, 635976, 6717600, 77482080, 969338880, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
a(n) +(-2*n+1)*a(n-1) +n*(n-2)*a(n-2) +(2*n-7)*a(n-3) -(n-3)*(n-5)*a(n-4) = 0.

Formalization: the entry records a(1)=0, a(2)=1, a(3)=5, a(n) = n*a(n-1) + (n-1)! - (n-3)! for n ≥ 4,
and this recurrence is the definition of a(n) used here (with values in ℤ; the value a(0) = 0 is a
placeholder and is not used). `main` is the corrected recurrence (n ≥ 7): on the data the left side
of the recurrence as stated is 0 at n = 5 and 1 at n = 6, and it vanishes from n = 7 on; for example
at n = 7: (1)*(7668) + (-13)*(996) + (35)*(147) + (7)*(25) + (-8)*(5) = 0.
-/

namespace OMA.S_oeis_a121639

/-- a(1)=0, a(2)=1, a(3)=5, a(n) = n*a(n-1) + (n-1)! - (n-3)! for n ≥ 4 (a(0) = 0 is a placeholder). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 5
  | (n + 4) => ((n : ℤ) + 4) * a (n + 3) + ((n + 3).factorial : ℤ) - ((n + 1).factorial : ℤ)

/-- The corrected recurrence (n ≥ 7): Mathar's recurrence, which fails at n = 6. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    a n + (-2 * (n : ℤ) + 1) * a (n - 1) + (n : ℤ) * ((n : ℤ) - 2) * a (n - 2) +
      (2 * (n : ℤ) - 7) * a (n - 3) - ((n : ℤ) - 3) * ((n : ℤ) - 5) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a121639
