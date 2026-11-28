import Mathlib

/-!
# A243662: Triangle read by rows: the reversed x = 1+q Narayana triangle at m=2.

Source: https://oeis.org/A243662
Credit: @agchua

Formula section of A243662:
  T(n,k) = (binomial(3*n+1,n) * binomial(n,k-1) * binomial(n-1,k-1)) / (binomial(3*n,k-1) * (3*n+1))
  = (A001764(n) * A001263(n,k) * k) / binomial(3*n,k-1) for 1 <= k <= n (conjectured).
The triangle is taken by the explicit formula of the same section,
  T(n,k) = binomial(3*n+1-k,n-k) * binomial(n,k-1) / n for 1 <= k <= n,
which agrees with all listed terms; by Lagrange inversion it is the coefficient of x^n*y^(k-1)
in the g.f. of the entry, the series reversion of x/((1 + x + x*y)*(1 + x)^2).
A001764(n) = binomial(3*n,n)/(2*n+1) and A001263(n,k) = C(n-1,k-1)*C(n,k-1)/k are taken from
their name lines. Offset 1; all quantities are in ℚ; both equalities are stated for 1 ≤ k ≤ n.
-/

namespace OMA.S_oeis_a243662

/-- A001764(n) = binomial(3*n,n)/(2*n+1). -/
def A001764 (n : ℕ) : ℚ := ((3 * n).choose n : ℚ) / (2 * n + 1)

/-- Narayana numbers A001263(n,k) = C(n-1,k-1)*C(n,k-1)/k. -/
def A001263 (n k : ℕ) : ℚ := ((n - 1).choose (k - 1) : ℚ) * (n.choose (k - 1) : ℚ) / k

/-- T(n,k) = binomial(3*n+1-k,n-k) * binomial(n,k-1) / n. -/
def T (n k : ℕ) : ℚ := ((3 * n + 1 - k).choose (n - k) : ℚ) * (n.choose (k - 1) : ℚ) / n

/-- The conjectured formula, both equalities, for 1 ≤ k ≤ n. -/
theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    T n k = ((3 * n + 1).choose n : ℚ) * (n.choose (k - 1) : ℚ) * ((n - 1).choose (k - 1) : ℚ)
        / (((3 * n).choose (k - 1) : ℚ) * (3 * n + 1)) ∧
      ((3 * n + 1).choose n : ℚ) * (n.choose (k - 1) : ℚ) * ((n - 1).choose (k - 1) : ℚ)
          / (((3 * n).choose (k - 1) : ℚ) * (3 * n + 1))
        = A001764 n * A001263 n k * k / ((3 * n).choose (k - 1) : ℚ) := by
  sorry

end OMA.S_oeis_a243662
