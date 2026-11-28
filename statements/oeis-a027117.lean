import Mathlib

/-!
# A027117: a(n) = A027113(n, n+4).

Source: https://oeis.org/A027117
Credit: @JeremyDevs

Formalizes the recurrence conjectured by Colin Barker (Feb 20 2016) in the FORMULA section of
OEIS A027117: a(n) = 4*a(n-1)-5*a(n-2)+2*a(n-3)-a(n-4)+2*a(n-5)-a(n-6) for n>9.

Conventions:
* A027113 is the triangular array T given by rows (row n >= 0 has the 2n+1 entries T(n,0), ...,
  T(n,2n)) defined by its name: T(n,0) = 1 for n >= 0, T(n,1) = 1, T(n,2) = 2 for n >= 1 and
  for n >= 2, T(n,k) = T(n-1,k-3) + T(n-1,k-2) + T(n-1,k-1) for 3 <= k <= 2n-1,
  T(n,2n) = T(n-1,2n-3) + T(n-1,2n-2). Rows: 1; 1,1,2; 1,1,2,4,3; 1,1,2,4,7,9,7; ...
  `T n k` is this array; outside the triangle (k > 2n) it is given the value 0, which is never
  used by the rules above nor by the sequence.
* The sequence has offset 4 and a(n) = T(n, n+4), which lies in the triangle exactly for n >= 4;
  data 16, 59, 155, 352, 738, 1475, ... `a n` is `T n (n + 4)` for every n.
* The recurrence is asserted for every n > 9, as in the source; then n-6 >= 4, so every term
  used is a term of the sequence and all indices are natural numbers. The terms are integers.
* The generating function conjectured by Barker in the same comment,
  x^4*(16-5*x-x^2-5*x^3+3*x^4) / ((1-x)^3*(1-x-x^2-x^3)), is not stated separately: given the
  first six terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a027117

/-- A027113: T(n,0) = 1, T(n,1) = 1 and T(n,2) = 2 for n >= 1, and for n >= 2,
T(n,k) = T(n-1,k-3) + T(n-1,k-2) + T(n-1,k-1) for 3 <= k <= 2n-1,
T(n,2n) = T(n-1,2n-3) + T(n-1,2n-2). (Value 0 for k > 2n.) -/
def T : ℕ → ℕ → ℤ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 1 => 1
  | _ + 1, 2 => 2
  | n + 1, k + 3 =>
    if k + 3 ≤ 2 * (n + 1) - 1 then T n k + T n (k + 1) + T n (k + 2)
    else if k + 3 = 2 * (n + 1) then T n k + T n (k + 1)
    else 0

/-- A027117 (offset 4): a(n) = T(n, n+4). -/
def a (n : ℕ) : ℤ := T n (n + 4)

/-- For every n > 9, a(n) = 4a(n-1) - 5a(n-2) + 2a(n-3) - a(n-4) + 2a(n-5) - a(n-6). -/
theorem main : ∀ n : ℕ, 9 < n →
    a n = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3) - a (n - 4) + 2 * a (n - 5)
      - a (n - 6) := by
  sorry

end OMA.S_oeis_a027117
