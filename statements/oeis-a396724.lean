import Mathlib

/-!
# A396724: a(n) = (-4^n/2) p(n, -3/2), p(n,x) the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1

Source: https://oeis.org/A396724 (conjecture by R. J. Mathar, Jun 30 2026)

`p(n, x)` is the Lagrange interpolating polynomial (over `ℚ`, of degree at most `n`) through the
`n + 1` points `(1, 0)` and `(k, 1)` for `k = 2..n+1`. In Mathlib this is
`Lagrange.interpolate s v r` with node set `s = {1, ..., n+1}` (natural numbers), node map
`v k = k` in `ℚ`, and values `r 1 = 0`, `r k = 1` otherwise. The sequence is
`a(n) = (-4^n/2) * p(n, -3/2)` (offset 0), taken in `ℚ`.

The conjecture: D-finite with recurrence `n*a(n) +2*(-4*n-3)*a(n-1) +8*(2*n+3)*a(n-2) = 0`,
stated for `n >= 2`, where every index is defined.
Controls from the entry: a(0..4) = 0, 5, 55, 430, 2875.
-/

namespace OMA.S_oeis_a396724

open Polynomial

/-- The Lagrange interpolating polynomial through `(1, 0)` and `(k, 1)` for `k = 2..n+1`. -/
noncomputable def p (n : ℕ) : ℚ[X] :=
  Lagrange.interpolate (Finset.Icc 1 (n + 1)) (fun k : ℕ => (k : ℚ)) (fun k => if k = 1 then 0 else 1)

/-- A396724(n) = (-4^n/2) * p(n, -3/2). -/
noncomputable def a (n : ℕ) : ℚ := -(4 : ℚ) ^ n / 2 * (p n).eval (-3 / 2)

theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℚ) * a n + 2 * (-4 * (n : ℚ) - 3) * a (n - 1) + 8 * (2 * (n : ℚ) + 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a396724
