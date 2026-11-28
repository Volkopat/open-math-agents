import Mathlib

/-!
# A026975: a(n) = Sum_{k=0..n} (k+1) * A026648(n,k).

Source: https://oeis.org/A026975
Credit: @JeremyDevs

Formalizes the recurrence conjectured by Colin Barker (Feb 18 2016) in the FORMULA section of
OEIS A026975: a(n) = 8*a(n-2)-12*a(n-4)-16*a(n-6)-4*a(n-8) for n>7.

Conventions:
* A026648 is the triangular array T read by rows (rows n >= 0, columns 0 <= k <= n) defined by
  its name: T(n,0) = T(n,n) = 1 for n >= 0; for n >= 2 and 1 <= k <= n-1,
  T(n,k) = T(n-1,k-1) + T(n-2,k-1) + T(n-1,k) if n is even and k is odd, else
  T(n,k) = T(n-1,k-1) + T(n-1,k). Rows: 1; 1,1; 1,3,1; 1,4,4,1; 1,6,8,6,1; ...
  `T n k` is this array; outside the triangle (k > n) it is given the value 0, which is never
  used below.
* The sequence has offset 0 and a(n) = Sum_{k=0..n} (k+1)*T(n,k); data 1, 3, 10, 25, 66, 154, ...
* The recurrence is asserted for every n > 7, as in the source; all indices used are then
  natural numbers. The terms are integers.
* The generating function conjectured by Barker in the same comment,
  (1+3*x+2*x^2+x^3-2*x^4-10*x^5-2*x^7) / (1-4*x^2-2*x^4)^2, is not stated separately: given the
  first eight terms it is the same assertion as the recurrence.
-/

namespace OMA.S_oeis_a026975

/-- A026648: T(n,0) = T(n,n) = 1; for n >= 2 and 1 <= k <= n-1,
T(n,k) = T(n-1,k-1) + T(n-2,k-1) + T(n-1,k) if n is even and k is odd, else
T(n,k) = T(n-1,k-1) + T(n-1,k). (Value 0 for k > n.) -/
def T : ℕ → ℕ → ℤ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | 1, k + 1 => if k = 0 then 1 else 0
  | n + 2, k + 1 =>
    if k + 1 = n + 2 then 1
    else if k + 1 < n + 2 then
      (if (n + 2) % 2 = 0 ∧ (k + 1) % 2 = 1 then T (n + 1) k + T n k + T (n + 1) (k + 1)
       else T (n + 1) k + T (n + 1) (k + 1))
    else 0

/-- A026975 (offset 0): a(n) = Sum_{k=0..n} (k+1)*T(n,k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), ((k : ℤ) + 1) * T n k

/-- For every n > 7, a(n) = 8*a(n-2) - 12*a(n-4) - 16*a(n-6) - 4*a(n-8). -/
theorem main : ∀ n : ℕ, 7 < n →
    a n = 8 * a (n - 2) - 12 * a (n - 4) - 16 * a (n - 6) - 4 * a (n - 8) := by
  sorry

end OMA.S_oeis_a026975
