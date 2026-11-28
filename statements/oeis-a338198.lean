import Mathlib

/-!
# A338198: T(n,k) = ((k+1)*2^(n-k)-(k-2)*(-1)^(n-k))/3, and its matrix inverse
Source: https://oeis.org/A338198 (Werner Schulte, Oct 15 2020)

T(n,k) = ((k+1)*2^(n-k) - (k-2)*(-1)^(n-k))/3 for 0 <= k <= n and T(n,k) = 0 for k > n,
seen as an infinite lower triangular matrix; values are taken in the rationals.

Conjecture: the matrix inverse M of T is given by M(i,j) = 0 if j > i, M(n,n) = 1,
M(n,n-1) = 1-n for n > 0, and M(n,k) = (-1)^(n-k)*(k^2-2)*(n-2)!/k! for 0 <= k <= n-2.
We state that this explicit M satisfies T*M = 1 and M*T = 1 (the products are finite sums since
both matrices are lower triangular).
-/

namespace OMA.S_oeis_a338198

/-- A338198, zero above the diagonal. -/
def T (n k : ℕ) : ℚ :=
  if k ≤ n then (((k : ℚ) + 1) * 2 ^ (n - k) - ((k : ℚ) - 2) * (-1) ^ (n - k)) / 3 else 0

/-- The conjectured inverse. -/
def M (n k : ℕ) : ℚ :=
  if n < k then 0
  else if k = n then 1
  else if k + 1 = n then 1 - (n : ℚ)
  else (-1) ^ (n - k) * ((k : ℚ) ^ 2 - 2) * ((n - 2).factorial : ℚ) / (k.factorial : ℚ)

theorem main : ∀ n k : ℕ,
    (∑ j ∈ Finset.range (n + 1), T n j * M j k) = (if n = k then 1 else 0) ∧
    (∑ j ∈ Finset.range (n + 1), M n j * T j k) = (if n = k then 1 else 0) := by
  sorry

end OMA.S_oeis_a338198
