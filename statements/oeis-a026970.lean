import Mathlib

/-!
# A026970: a(n) = Sum_{k=0..n} (k+1) * A026637(n,k)

Source: https://oeis.org/A026970
Credit: @ivillar

Clark Kimberling's sequence (offset 0). A026637 is the triangular array with T(n,0) = T(n,n) = 1
for n >= 0, T(n,1) = T(n,n-1) = floor((3*n-1)/2) for n >= 1, and T(n,k) = T(n-1,k-1) + T(n-1,k)
for 2 <= k <= n-2, n >= 4 (rows 1, 1 1, 1 2 1, 1 4 4 1, 1 5 8 5 1, ...).

Conjectures from Colin Barker, Feb 18 2016:
  a(n) = -((-1)^n-2^(n+2)+3)*(n+2)/6 for n>0.
  a(n) = 4*a(n-1)-2*a(n-2)-8*a(n-3)+7*a(n-4)+4*a(n-5)-4*a(n-6) for n>6.
  G.f.: (1-x-2*x^2+7*x^3-7*x^4-4*x^5+4*x^6) / ((1-x)^2*(1+x)^2*(1-2*x)^2).
The closed form is stated in ℚ, the recurrence in ℤ, and the g.f. as a power series over ℚ.
-/

namespace OMA.S_oeis_a026970

/-- A026637: T(n,0) = T(n,n) = 1 for n >= 0, T(n,1) = T(n,n-1) = floor((3*n-1)/2) for n >= 1, and
T(n,k) = T(n-1,k-1) + T(n-1,k) for 2 <= k <= n-2 (n >= 4); T(n,k) = 0 for k > n. -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
    if k = 0 ∨ k = n + 1 then 1
    else if n + 1 < k then 0
    else if k = 1 ∨ k = n then (3 * (n + 1) - 1) / 2
    else T n (k - 1) + T n k

/-- A026970: a(n) = Sum_{k=0..n} (k+1) * A026637(n,k) (offset 0). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (k + 1) * T n k

/-- The conjectured g.f. (1-x-2x^2+7x^3-7x^4-4x^5+4x^6) / ((1-x)^2*(1+x)^2*(1-2x)^2) over ℚ. -/
noncomputable def G : PowerSeries ℚ :=
  (1 - PowerSeries.X - 2 * PowerSeries.X ^ 2 + 7 * PowerSeries.X ^ 3 - 7 * PowerSeries.X ^ 4 -
      4 * PowerSeries.X ^ 5 + 4 * PowerSeries.X ^ 6) *
    ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2)⁻¹

/-- Barker's conjectures: the closed form (n > 0), the recurrence (n > 6) and the g.f. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℚ) = -((-1) ^ n - 2 ^ (n + 2) + 3) * (n + 2) / 6) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 4 * a (n - 1) - 2 * a (n - 2) - 8 * a (n - 3) + 7 * a (n - 4) +
      4 * a (n - 5) - 4 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) = G := by
  sorry

end OMA.S_oeis_a026970
