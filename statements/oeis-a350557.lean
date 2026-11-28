import Mathlib

/-!
# A350557: a triangle whose signed version is conjectured to invert A350512
Source: https://oeis.org/A350557 (Werner Schulte, Jan 05 2022)

A350557: T(n,0) = (2n)!/(2^n n!) and, for 0 < k <= n,
T(n,k) = (Sum_{i=k..n} binomial(i-1,k-1)*2^i*i!/(2i)!) * (2n)!/(2^n n!).
A350512: L(n,0) = 1 and L(n,k) = binomial(n-1,k-1)*(2k(n-k)+n)/k for 0 < k <= n.
Both are lower triangular (entries with k > n are 0); values are taken in the rationals.

Conjecture: M(n,k) = (-1)^(n-k)*T(n,k) is the matrix inverse of A350512.
As both matrices are lower triangular, the products are finite sums, and we state that
L*M and M*L are both the identity matrix.
-/

namespace OMA.S_oeis_a350557

/-- (2n)!/(2^n n!). -/
def df (n : ℕ) : ℚ := ((2 * n).factorial : ℚ) / (2 ^ n * (n.factorial : ℚ))

/-- A350557. -/
def T (n k : ℕ) : ℚ :=
  if k = 0 then df n
  else (∑ i ∈ Finset.Icc k n, ((i - 1).choose (k - 1) : ℚ) * 2 ^ i * (i.factorial : ℚ) /
    ((2 * i).factorial : ℚ)) * df n

/-- The signed triangle M(n,k) = (-1)^(n-k)*T(n,k), zero above the diagonal. -/
def M (n k : ℕ) : ℚ := if k ≤ n then (-1) ^ (n - k) * T n k else 0

/-- A350512, zero above the diagonal. -/
def L (n k : ℕ) : ℚ :=
  if k ≤ n then (if k = 0 then 1 else ((n - 1).choose (k - 1) : ℚ) *
    (2 * (k : ℚ) * ((n : ℚ) - k) + n) / k) else 0

theorem main : ∀ n k : ℕ,
    (∑ j ∈ Finset.range (n + 1), L n j * M j k) = (if n = k then 1 else 0) ∧
    (∑ j ∈ Finset.range (n + 1), M n j * L j k) = (if n = k then 1 else 0) := by
  sorry

end OMA.S_oeis_a350557
