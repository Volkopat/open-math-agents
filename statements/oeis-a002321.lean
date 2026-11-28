import Mathlib

/-!
# A002321: Mertens's function: Sum_{k=1..n} mu(k), where mu is the Moebius function A008683.

Source: https://oeis.org/A002321
Credit: @HaZeLnU7

Conjecture stated in A002321: a(n)+2 = A192763(n,1) for n>1, and A192763(1,k) for k>1.

A192763 (https://oeis.org/A192763) is the symmetric square array T(n,k), n, k >= 1,
defined in its formula section and first Mathematica program (Granvik and Gerard):
  T(1,1) = 1, T(1,2) = T(2,1) = 2,
  T(1,k) = (-T(1,k-1) - Sum_{i=2..k-1} T(i,k)) / (k+1) + T(1,k-1)   for k >= 3,
  T(n,1) = (-T(n-1,1) - Sum_{i=2..n-1} T(n,i)) / (n+1) + T(n-1,1)   for n >= 3,
  T(n,k) = -Sum_{i=1..k-1} T(n-i,k)                               for n >= k >= 2,
  T(n,k) = -Sum_{i=1..n-1} T(k-i,n)                               for 2 <= n < k.
The formula allows T(1,1) = 1 or 3; the program uses 1. No other entry depends on
T(1,1). The divisions are exact rational divisions, so T takes values in ℚ; indices
outside n, k >= 1 give 0. The recursion terminates: every entry depends only on entries
with a smaller max(n,k), or, at the same max(n,k), on entries of lower rank, where
rank 2 is the diagonal, rank 1 is the first row and column, and rank 0 is the rest.
-/

namespace OMA.S_oeis_a002321

/-- Mertens's function A002321: M(n) = Sum_{k=1..n} mu(k). -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k

/-- The array A192763, following its formula and first Mathematica program. -/
def T (n k : ℕ) : ℚ :=
  if n = 0 ∨ k = 0 then 0
  else if n = 1 ∧ k = 1 then 1
  else if (n = 1 ∧ k = 2) ∨ (n = 2 ∧ k = 1) then 2
  else if n = 1 then
    (-T 1 (k - 1) - ∑ i ∈ (Finset.Ico 2 k).attach, T i k) / (k + 1) + T 1 (k - 1)
  else if k = 1 then
    (-T (n - 1) 1 - ∑ i ∈ (Finset.Ico 2 n).attach, T n i) / (n + 1) + T (n - 1) 1
  else if k ≤ n then
    -∑ i ∈ (Finset.Ico 1 k).attach, T (n - i) k
  else
    -∑ i ∈ (Finset.Ico 1 n).attach, T (k - i) n
termination_by 3 * max n k + (if n = k then 2 else if n = 1 ∨ k = 1 then 1 else 0)
decreasing_by
  all_goals
    first
    | (have hi := Finset.mem_Ico.mp (Subtype.property ‹_›); split_ifs <;> omega)
    | (split_ifs <;> omega)

/-- The conjecture from A002321: for n > 1, M(n) + 2 is both the entry T(n,1) of the
first column and the entry T(1,n) of the first row of A192763. -/
theorem main : ∀ n : ℕ, 1 < n → T n 1 = (mertens n : ℚ) + 2 ∧ T 1 n = (mertens n : ℚ) + 2 := by
  sorry

end OMA.S_oeis_a002321
