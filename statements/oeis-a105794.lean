import Mathlib

/-!
# A105794: inverse of a generalized Stirling number triangle of first kind

Source: https://oeis.org/A105794 (conjectures by Werner Schulte, Feb 15 2025)

A105793 is the triangle with e.g.f. `(1+y)^(1+x)`: its row `n` has g.f.
`n! * binomial(x+1, n) = (x+1)*x*(x-1)*...*(x-n+2)`, the falling factorial of `x+1` with `n`
factors, i.e. `(descPochhammer ℚ n).comp (X + 1)`, and `A105793(n,k)` is the coefficient of
`x^k` there (so it vanishes for `k > n`, and `A105793(n,n) = 1`). A105794 is the inverse matrix
`T`: `Sum_{j=0..n} A105793(n,j) * T(j,k) = [n = k]` for all `n, k` (the sum over `j <= n` is the
full matrix product, since `A105793(n,j) = 0` for `j > n`). As A105793 is lower unitriangular,
this condition determines `T` uniquely; the statement asserts that such a `T` exists and that
every such `T` satisfies both conjectures. All values are taken in `ℚ`.

Conjecture 1: `Sum_{k=0..n} (-1)^(n-k) * T(n,k) * (k+m)!/m! = (m+2)^n` for `m >= 0`.
Conjecture 2: `(-1)^n - B(n) = Sum_{k=1..n} (-1)^k * T(n,k) * (k-1)!/(k+1)`, where
`B(n) = B(n,0)` is the `n`-th Bernoulli number, so `B(1) = -1/2` (Mathlib's `bernoulli`).
Both are stated for all `n >= 0`.
-/

namespace OMA.S_oeis_a105794

open Polynomial

/-- A105793: the coefficient of `x^k` in `(x+1)*x*(x-1)*...*(x-n+2)` (`n` factors). -/
noncomputable def A105793 (n k : ℕ) : ℚ := ((descPochhammer ℚ n).comp (X + 1)).coeff k

/-- `T` is the inverse of the triangle A105793. -/
def IsInverse (T : ℕ → ℕ → ℚ) : Prop :=
  ∀ n k : ℕ, ∑ j ∈ Finset.range (n + 1), A105793 n j * T j k = if n = k then 1 else 0

theorem main : (∃ T : ℕ → ℕ → ℚ, IsInverse T) ∧
    ∀ T : ℕ → ℕ → ℚ, IsInverse T →
      (∀ n m : ℕ, ∑ k ∈ Finset.range (n + 1),
          (-1 : ℚ) ^ (n - k) * T n k * ((k + m).factorial / m.factorial) = ((m : ℚ) + 2) ^ n) ∧
      (∀ n : ℕ, (-1 : ℚ) ^ n - _root_.bernoulli n =
          ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ k * T n k * ((k - 1).factorial / (k + 1))) := by
  sorry

end OMA.S_oeis_a105794
