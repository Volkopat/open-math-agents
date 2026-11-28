import Mathlib

/-!
# A348482: T(n,k) = (Sum_{i=k..n} i!)/k! for 0 <= k <= n
Source: https://oeis.org/A348482 (Werner Schulte, Oct 20 2021)

T(n,k) = (Sum_{i=k..n} i!)/k!, taken in the rationals (the values are integers), and the row
polynomials are p(n,x) = Sum_{k=0..n} T(n,k)*x^k. The entry states three conjectures:
1. T(n,1) = T(n,0) - 1 = Sum_{k=0..n-1} T(n,k)/(k+2) for n > 0;
2. (c) p(n,x) = (x+1)*p(n-1,x) + 1 + Sum_{i=1..n-1} (d/dx)^i p(n-1,x) for n > 0;
3. the alternating row sums p(n,-1) equal A173184(n) for n >= 0, where A173184 is the sequence of
   partial sums of A000166 (the derangement numbers, numDerangements in Mathlib).
-/

namespace OMA.S_oeis_a348482

open Polynomial

/-- A348482. -/
def T (n k : ℕ) : ℚ := (∑ i ∈ Finset.Icc k n, (i.factorial : ℚ)) / (k.factorial : ℚ)

/-- Row polynomials of A348482. -/
noncomputable def p (n : ℕ) : ℚ[X] := ∑ k ∈ Finset.range (n + 1), C (T n k) * X ^ k

/-- A173184: partial sums of the derangement numbers A000166. -/
def A173184 (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), numDerangements j

theorem main :
    (∀ n : ℕ, 0 < n → T n 1 = T n 0 - 1 ∧
        T n 0 - 1 = ∑ k ∈ Finset.range n, T n k / ((k : ℚ) + 2)) ∧
    (∀ n : ℕ, 0 < n → p n = (X + 1) * p (n - 1) + 1 +
        ∑ i ∈ Finset.Icc 1 (n - 1), (derivative)^[i] (p (n - 1))) ∧
    (∀ n : ℕ, (p n).eval (-1) = (A173184 n : ℚ)) := by
  sorry

end OMA.S_oeis_a348482
