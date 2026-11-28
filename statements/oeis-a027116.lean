import Mathlib

/-!
# A027116: a(n) = A027113(n, n+3)

Source: https://oeis.org/A027116 and https://oeis.org/A027113
Credit: @jagong-cmu

A027113 is the triangular array T given by rows: T(n,0)=1 for n >= 0, T(n,1)=1,
T(n,2)=2 for n >= 1 and for n >= 2, T(n,k)=T(n-1,k-3)+T(n-1,k-2)+T(n-1,k-1) for
3<=k<=2n-1, T(n, 2n)=T(n-1,2n-3)+T(n-1,2n-2). Row n has the entries k = 0..2n.
A027116 is a(n) = T(n, n+3), with offset 3.

Formalizes Colin Barker's OEIS A027116 conjecture (Feb 20 2016):
`a(n) = 3*a(n-1)-2*a(n-2)-a(n-4)+a(n-5) for n>7.`
Barker also gives the g.f. `x^3*(7+2*x+x^2-2*x^3) / ((1-x)^2*(1-x-x^2-x^3))`.
That g.f. is the same claim as the recurrence for `n > 7`, together with the terms
a(3), ..., a(7), so only the recurrence is stated.

Conventions:
* `T n k` follows the rules above literally. Entries outside a row (k > 2n) do not occur
  in the OEIS triangle; here they are set to 0, and they are never used by the rules
  for the entries of the triangle.
* `a n = T n (n + 3)`. For `n >= 3` the index `n + 3` is at most `2n`, so it is an entry of row `n`.
* The recurrence is stated in `ℤ` (to avoid ℕ subtraction) for every `n >= 8`,
  which is the range `n > 7` of the conjecture (all indices are then `>= 3`).
-/

namespace OMA.S_oeis_a027116

/-- The triangle A027113 (row `n` has the entries `k = 0..2n`; other values are 0). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
    if k = 0 then 1
    else if k = 1 then 1
    else if k = 2 then 2
    else if k ≤ 2 * (n + 1) - 1 then T n (k - 3) + T n (k - 2) + T n (k - 1)
    else if k = 2 * (n + 1) then T n (2 * (n + 1) - 3) + T n (2 * (n + 1) - 2)
    else 0

/-- A027116: `a(n) = T(n, n+3)`. -/
def a (n : ℕ) : ℕ := T n (n + 3)

/-- For all `n > 7`: `a(n) = 3*a(n-1) - 2*a(n-2) - a(n-4) + a(n-5)`. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2) - a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a027116
