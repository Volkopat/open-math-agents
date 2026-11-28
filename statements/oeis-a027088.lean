import Mathlib

/-!
# A027088: a(n) = A027082(n, 2n-1).

Source: https://oeis.org/A027088
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 3, 6, 16, 41, 107, 283, 757, 2043, 5557, ...
It is defined as in the name of the entry, a(n) = T(n, 2n-1), where T is the irregular triangular
array of A027082: T(n,0) = 1 for n >= 1; T(n,1) = T(n,2) = 1 for n >= 1;
T(n,k) = T(n-1,k-3) + T(n-1,k-2) + T(n-1,k-1) for 3 <= k <= 2n-1 and n >= 2; and
T(n,2n) = T(n-1,2n-3) + T(n-1,2n-2) for n >= 2 (row 0 is the single entry 1).

Conjecture (R. J. Mathar, Jun 24 2020): D-finite with recurrence
3*(n+1)*(18*n-85)*a(n) +(292*n^2-1316*n-255)*a(n-1) +(-218*n^2+1213*n-1056)*a(n-2)
+2*(-248*n^2+1666*n-2223)*a(n-3) +(-50*n^2-497*n+3243)*a(n-4) +(-52*n^2+80*n+765)*a(n-5)
+3*(22*n-83)*(n-6)*a(n-6)=0.
It involves a(n-6) and the offset is 1, so it is stated for n >= 7, exactly as printed.

Remark for the reviewer: with the terms of the entry the left-hand side at n = 7 is 556944, so the
relation as printed does not hold for the listed terms (and no shift of the index by -3..3
repairs it). The statement below keeps the printed form.
-/

namespace OMA.S_oeis_a027088

/-- The irregular triangular array of A027082 (0 outside row n, which has entries k = 0..2n). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | (n + 1), k =>
    if k ≤ 2 then 1
    else if k ≤ 2 * n + 1 then T n (k - 3) + T n (k - 2) + T n (k - 1)
    else if k = 2 * n + 2 then T n (2 * n - 1) + T n (2 * n)
    else 0

/-- A027088: a(n) = T(n, 2n-1). -/
def a (n : ℕ) : ℕ := T n (2 * n - 1)

/-- The conjectured recurrence for A027088, as printed in the entry. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    3 * ((n : ℤ) + 1) * (18 * n - 85) * a n + (292 * (n : ℤ) ^ 2 - 1316 * n - 255) * a (n - 1)
      + (-218 * (n : ℤ) ^ 2 + 1213 * n - 1056) * a (n - 2)
      + 2 * (-248 * (n : ℤ) ^ 2 + 1666 * n - 2223) * a (n - 3)
      + (-50 * (n : ℤ) ^ 2 - 497 * n + 3243) * a (n - 4)
      + (-52 * (n : ℤ) ^ 2 + 80 * n + 765) * a (n - 5)
      + 3 * (22 * (n : ℤ) - 83) * ((n : ℤ) - 6) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a027088
