import Mathlib

/-!
# A159856: Triangle read by rows: T(n,0) = n+1, T(n,k) = 2*T(n-1,k) - T(n-1,k-1), T(n,k) = 0 if k > n and if k < 0

Source: https://oeis.org/A159856
Credit: @ivillar

Philippe Deléham's triangle (rows n ≥ 0, columns 0 ≤ k ≤ n).

Conjecture (R. J. Mathar, May 31 2009): Sum_{k=0..n} |T(n,k)| = A047926(n), where
A047926(n) = (3^(n+1) + 2*n + 1)/4 (offset 0). (The entry writes the summation index as i; the
summand is |T(n,i)|.) The identity is stated in ℚ, with the exact division by 4.
-/

namespace OMA.S_oeis_a159856

/-- T(n,0) = n+1 and T(n,k) = 2*T(n-1,k) - T(n-1,k-1) for k ≥ 1; T(0,k) = 0 for k ≥ 1, so that
T(n,k) = 0 whenever k > n, as in the definition. -/
def T : ℕ → ℕ → ℤ
  | n, 0 => n + 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => 2 * T n (k + 1) - T n k

/-- Mathar's conjecture: the row sums of |T(n,k)| are A047926(n) = (3^(n+1) + 2*n + 1)/4. -/
theorem main : ∀ n : ℕ,
    ((∑ k ∈ Finset.range (n + 1), |T n k| : ℤ) : ℚ) = (3 ^ (n + 1) + 2 * n + 1) / 4 := by
  sorry

end OMA.S_oeis_a159856
