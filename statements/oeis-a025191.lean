import Mathlib

/-!
# A025191: row sums of the left half of the triangle A025177

Source: https://oeis.org/A025191 (conjectures in the entry, author not named)

`a(n) = Sum_{k=0..n} T(n,k)` (offset 0), where `T` is the array A025177, the first differences
in the `n,n` direction of the trinomial array A027907: `T(n,k) = t(n,k) - t(n-1,k-1)`, where
`t(n,k)` is the coefficient of `x^k` in `(1+x+x^2)^n` and `t(n-1,k-1) = 0` when `n = 0` or
`k = 0`. (This is the array with g.f. `(1-y*z)/(1-z*(1+y+y^2))` given in A025177.)

`A027914(n) = t(n,0) + t(n,1) + ... + t(n,n)`, and `A081673(n)` is `n!` times the coefficient
of `x^n` in the e.g.f. `exp(3*x) - exp(x)*(1 - BesselI_0(2*x))`, where
`BesselI_0(2*x) = Sum_{j>=0} x^(2*j)/(j!)^2`. All values are taken in `ℚ`.

The conjectures, for `n >= 1` (where `n-1` is a valid index):
`a(n) = A027914(n) - A027914(n-1) = (A081673(n) - A081673(n-1))/2`.
-/

namespace OMA.S_oeis_a025191

open Polynomial

/-- The trinomial array A027907: the coefficient of `x^k` in `(1+x+x^2)^n`. -/
noncomputable def t (n k : ℕ) : ℚ := ((1 + X + X ^ 2 : ℚ[X]) ^ n).coeff k

/-- The array A025177: `T(n,k) = t(n,k) - t(n-1,k-1)`. -/
noncomputable def T (n k : ℕ) : ℚ := t n k - if 1 ≤ n ∧ 1 ≤ k then t (n - 1) (k - 1) else 0

/-- A025191: `a(n) = Sum_{k=0..n} T(n,k)`. -/
noncomputable def a (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), T n k

/-- A027914: `t(n,0) + t(n,1) + ... + t(n,n)`. -/
noncomputable def A027914 (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), t n k

/-- The e.g.f. `exp(3*x) - exp(x)*(1 - BesselI_0(2*x))` of A081673. -/
noncomputable def egf : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (3 : ℚ) ^ n / n.factorial) - PowerSeries.exp ℚ *
    (1 - PowerSeries.mk fun n => if Even n then 1 / ((n / 2).factorial : ℚ) ^ 2 else 0)

/-- A081673: `n!` times the coefficient of `x^n` in `egf`. -/
noncomputable def A081673 (n : ℕ) : ℚ := n.factorial * PowerSeries.coeff n egf

theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = A027914 n - A027914 (n - 1) ∧ a n = (A081673 n - A081673 (n - 1)) / 2 := by
  sorry

end OMA.S_oeis_a025191
