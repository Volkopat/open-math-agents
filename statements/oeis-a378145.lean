import Mathlib

/-!
# A378145: Riordan triangle (1 + x * C(x), x * C(x)), where C(x) is g.f. of A000108.

Source: https://oeis.org/A378145
Credit: @agchua

Formula section of A378145 (entry by Werner Schulte, Nov 17 2024):
  Conjecture: Sum_{i=0..n-k} binomial(i+m-1, i) * T(n, i+k) = T(n+m, m+k) for m > 0.
  Conjecture: Sum_{k=0..n} (1 + floor(k/2)) * T(n, k) = A000108(n+1).
Offset 0: rows n >= 0, columns 0 <= k <= n. As the name says, T(n,k) is the coefficient of x^n in
(1 + x*C(x)) * (x*C(x))^k, where C(x) = Sum_{n>=0} A000108(n) x^n is the g.f. of the Catalan
numbers (Mathlib's catalan), taken here as a power series over the integers. Both conjectures are
stated for all n and all columns 0 <= k <= n of the triangle, the first one for every m > 0.
-/

namespace OMA.S_oeis_a378145

/-- C(x): the g.f. of the Catalan numbers A000108, as a power series over ℤ. -/
noncomputable def Cx : PowerSeries ℤ := PowerSeries.mk fun n => (catalan n : ℤ)

/-- T(n,k) = A378145(n,k): the coefficient of x^n in (1 + x C(x)) (x C(x))^k. -/
noncomputable def T (n k : ℕ) : ℤ :=
  PowerSeries.coeff n ((1 + PowerSeries.X * Cx) * (PowerSeries.X * Cx) ^ k)

/-- Both conjectures of Werner Schulte. -/
theorem main :
    (∀ n k m : ℕ, k ≤ n → 0 < m →
      ∑ i ∈ Finset.range (n - k + 1), ((i + m - 1).choose i : ℤ) * T n (i + k) =
        T (n + m) (m + k)) ∧
    (∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), ((1 + k / 2 : ℕ) : ℤ) * T n k =
      (catalan (n + 1) : ℤ)) := by
  sorry

end OMA.S_oeis_a378145
