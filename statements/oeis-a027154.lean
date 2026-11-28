import Mathlib

/-!
# A027154: a(n) = Sum_{k=0..floor(n/2)} A027144(n-k, k).

Source: https://oeis.org/A027154
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 3, 5, 9, 15, 31, 49, 101, 163, 331, 533, ...
It is defined as in the name of the entry, a(n) = Sum_{k=0..floor(n/2)} T(n-k, k), where T is
Kimberling's triangular array A027144, given by rows:
T(n,0) = 1 for n >= 0, T(1,1) = 2;
for even n >= 2, T(n,k) = T(n-2,k-1) + T(n-1,k-1) + T(n-1,k) for 1 <= (odd k) <= n-1 and
T(n,k) = T(n-1,k-1) + T(n-1,k) for 2 <= (even k) <= n-2, T(n,n) = T(n-1,n-1);
for odd n >= 3, T(n,k) = T(n,k-1) + T(n-1,k-1) + T(n-1,k) for 1 <= (odd k) <= n-2 and
T(n,k) = T(n-1,k-1) + T(n-1,k) for 2 <= (even k) <= n-1, T(n,n) = T(n-1,n-1) + T(n,n-1).
(The name of A027144 prints "for odd n<=3"; the rows of that entry, 1; 1,2; 1,4,2; 1,6,6,8;
1,8,12,16,8; 1,10,20,48,24,32; ..., show that "odd n >= 3" is meant, and the definition below
reproduces them.)

Conjectures (Chai Wah Wu, Jun 10 2025):
a(n) = 2*a(n-2) + 3*a(n-4) + 4*a(n-6) for n > 5.
G.f.: -(x^2 + 1)*(2*x^3 + x + 1)/(4*x^6 + 3*x^4 + 2*x^2 - 1).
The generating function is stated in cleared form, as an identity of formal power series over ℤ.
-/

namespace OMA.S_oeis_a027154

/-- Kimberling's triangular array A027144 (rows n >= 0, entries 0 <= k <= n; 0 outside). -/
def T (n k : ℕ) : ℕ :=
  if k = 0 then 1
  else if n < k then 0
  else if n = 1 then 2
  else if n % 2 = 0 then
    if k = n then T (n - 1) (n - 1)
    else if k % 2 = 1 then T (n - 2) (k - 1) + T (n - 1) (k - 1) + T (n - 1) k
    else T (n - 1) (k - 1) + T (n - 1) k
  else
    if k = n then T (n - 1) (n - 1) + T n (n - 1)
    else if k % 2 = 1 then T n (k - 1) + T (n - 1) (k - 1) + T (n - 1) k
    else T (n - 1) (k - 1) + T (n - 1) k
termination_by (n, k)
decreasing_by all_goals omega

/-- A027154: a(n) = Sum_{k=0..floor(n/2)} T(n-k, k). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 2 + 1), T (n - k) k

open PowerSeries in
/-- The conjectured recurrence and generating function of A027154. -/
theorem main :
    (∀ n : ℕ, 6 ≤ n → a n = 2 * a (n - 2) + 3 * a (n - 4) + 4 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (4 * X ^ 6 + 3 * X ^ 4 + 2 * X ^ 2 - 1)
      = -((X ^ 2 + 1) * (2 * X ^ 3 + X + 1)) := by
  sorry

end OMA.S_oeis_a027154
