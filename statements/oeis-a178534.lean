import Mathlib

/-!
# A178534: Triangle T(n,k) read by rows. T(n,1) = A000045(n+1), k > 1: T(n,k) = (Sum_{i=1..k-1} T(n-i,k-1)) - (Sum_{i=1..k-1} T(n-i,k)).

Source: https://oeis.org/A178534
Credit: @esracummings31-blip

Rows n ≥ 1, columns 1 ≤ k ≤ n; as in the OEIS programs, T(n,k) = 0 for k > n.

Conjecture (R. J. Mathar, Sep 16 2017, "by extrapolating" from columns 3..8): the g.f. of the
k-th column is x^k (1 - x^2) / ((1 - x - x^2) (1 - x^k)), i.e. for every k ≥ 1
  (Sum_{n ≥ k} T(n,k) x^n) * (1 - x - x^2) * (1 - x^k) = x^k * (1 - x^2)
as formal power series.
-/

namespace OMA.S_oeis_a178534

/-- A178534 (with `T n k = 0` for `k > n`, and `T n 1 = F(n+1)`). -/
def T (n k : ℕ) : ℤ :=
  if k = 1 then (Nat.fib (n + 1) : ℤ)
  else if h : k = 0 ∨ n < k then 0
  else ∑ i : Fin (k - 1),
    (T (n - (i.1 + 1)) (k - 1) - T (n - (i.1 + 1)) k)
termination_by n
decreasing_by all_goals omega

/-- The g.f. of column `k` (entries of the triangle only, i.e. rows `n ≥ k`). -/
noncomputable def column (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if k ≤ n then T n k else 0

open PowerSeries in
theorem main : ∀ k : ℕ, 1 ≤ k →
    column k * ((1 - X - X ^ 2) * (1 - X ^ k)) = X ^ k * (1 - X ^ 2) := by
  sorry

end OMA.S_oeis_a178534
