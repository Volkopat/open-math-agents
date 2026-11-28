import Mathlib

/-!
# A134635: Row sums of triangle A134634.

Source: https://oeis.org/A134635
Credit: @agchua

R. J. Mathar, May 30 2014, in the formula section of A134635:
  Conjecture: (n+1)*a(n) +(-7*n+1)*a(n-1) +2*(7*n-8)*a(n-2) +4*(-2*n+5)*a(n-3)=0.
Offset of A134635: 0 (data 1, 2, 6, 18, 54, 164, 508, 1610, ...).

The triangle. A134634 (offset 0), name line: Triangle formed by Pascal's rule with borders = A000108.
Its formula line: Triangle, given right and left borders consist of the Catalan sequence, A000108;
then T(n,k) = T(n-1,k) + T(n-1,k-1). So for 0 <= k <= n: T(n,0) = T(n,n) = A000108(n), and
T(n,k) = T(n-1,k) + T(n-1,k-1) for 0 < k < n (rows 1; 1, 1; 2, 2, 2; 5, 4, 4, 5; 14, 9, 8, 9, 14).
Entries with k > n are set to 0; they are never used. A000108(n) is Mathlib's catalan n (the
Catalan numbers; catalan n = centralBinom n / (n + 1) by catalan_eq_centralBinom_div).
a(n) = Sum_{k=0..n} T(n,k).

The recurrence involves a(n-3), so it is stated for n >= 3 (every index is then >= the offset 0).
-/

namespace OMA.S_oeis_a134635

/-- The triangle A134634: Pascal's rule with both borders equal to the Catalan numbers A000108. -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then catalan 0 else 0
  | n + 1, k =>
    if k = 0 ∨ k = n + 1 then catalan (n + 1)
    else if k < n + 1 then T n k + T n (k - 1) else 0

/-- A134635(n): the sum of row n of A134634. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T n k

/-- Mathar's conjecture, for n >= 3. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 1) * (a n : ℤ) + (-7 * (n : ℤ) + 1) * (a (n - 1) : ℤ) +
      2 * (7 * (n : ℤ) - 8) * (a (n - 2) : ℤ) + 4 * (-2 * (n : ℤ) + 5) * (a (n - 3) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a134635
