import Mathlib

/-!
# A121636: Mathar's recurrence, corrected to n ≥ 5

Source: https://oeis.org/A121636
Credit: @ivillar

Status: false as stated at n = 4 (the left side is 1 at n = 4 on the OEIS data); `main` is the
corrected recurrence (n ≥ 5), which is proved. It follows from the recurrence with factorials
recorded in the entry, which is used as the definition here.

A121636 (offset 1): number of 2-cell columns starting at level 0 in all of deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column;
data 0, 1, 5, 23, 122, 754, 5364, 43308, 391824, 3929616, 43287840, 519711840, ...

Conjecture (R. J. Mathar, Jul 22 2022): D-finite with recurrence
a(n) +(-2*n+3)*a(n-1) +(n^2-5*n+7)*a(n-2) +(n-3)^2*a(n-3) = 0.

Formalization: the entry records a(1)=0, a(2)=1, a(n) = n*(n-2)! + (n-1)*a(n-1) for n ≥ 3, and this
recurrence is the definition of a(n) used here (with values in ℤ; the value a(0) = 0 is a placeholder
and is not used). `main` is the corrected recurrence (n ≥ 5): on the data the left side of the
recurrence as stated is 1 at n = 4, and it vanishes from n = 5 on; for example at n = 5:
(1)*(122) + (-7)*(23) + (7)*(5) + (4)*(1) = 0.
-/

namespace OMA.S_oeis_a121636

/-- a(1)=0, a(2)=1, a(n) = n*(n-2)! + (n-1)*a(n-1) for n ≥ 3 (a(0) = 0 is a placeholder). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (n + 3) => ((n : ℤ) + 3) * ((n + 1).factorial : ℤ) + ((n : ℤ) + 2) * a (n + 2)

/-- The corrected recurrence (n ≥ 5): Mathar's recurrence, which fails at n = 4. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    a n + (-2 * (n : ℤ) + 3) * a (n - 1) + ((n : ℤ) ^ 2 - 5 * (n : ℤ) + 7) * a (n - 2) +
      ((n : ℤ) - 3) ^ 2 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a121636
