import Mathlib

/-!
# A109263: A Catalan transform of F(n-1)-0^n.

Source: https://oeis.org/A109263 (conjecture by R. J. Mathar, Nov 09 2012)

`a(n)` (offset 0) is the coefficient of `x^n` in the Catalan transform of `b(n) = F(n-1) - 0^n`.
The Catalan transform of a sequence with g.f. `G(x)` has g.f. `G(x c(x))`, where `c(x)` is the g.f. of
the Catalan numbers A000108 (this gives the entry's g.f. `x^2c(x)^2/(1-xc(x)-x^2c(x)^2)`). Here
`b(0) = F(-1) - 1 = 0`, `b(1) = F(0) = 0` and `b(n) = F(n-1)` for `n >= 2`, so
`G(x) = Sum_{n>=0} b(n) x^n = x^2/(1-x-x^2)`. Over `ℚ`, `c` is Mathlib's `catalanSeries` mapped to `ℚ`,
`1/(1-x-x^2)` is the power-series inverse (constant term `1`), and `G(x c(x))` is `PowerSeries.subst`
(the inner series `x c(x)` has zero constant term).

The conjecture, stated for `n >= 4`. The entry gives no range; at `n = 3`, the first index
where every term is defined, the left side is `0*3 + 2*(-1)*1 + 8*0 + 2*0 = -2`, not `0` (data
`0, 0, 1, 3`), so the identity is stated from `n = 4` on, the range on which such recurrences from
the g.f. are meant:
Conjecture: n*(n-3)*a(n) +2*(-4*n^2+15*n-10)*a(n-1) +(15*n^2-69*n+80)*a(n-2) +2*(n-2)*(2*n-5)*a(n-3)=0.
-/

namespace OMA.S_oeis_a109263

open PowerSeries

/-- The generating function `c(x)` of the Catalan numbers A000108 (over `ℚ`). -/
noncomputable def c : PowerSeries ℚ := PowerSeries.map (Nat.castRingHom ℚ) catalanSeries

/-- `G(x) = x^2/(1-x-x^2)`, the generating function of `F(n-1) - 0^n`. -/
noncomputable def G : PowerSeries ℚ := X ^ 2 * (1 - X - X ^ 2)⁻¹

/-- The generating function of the sequence: the Catalan transform `G(x c(x))`. -/
noncomputable def A : PowerSeries ℚ := G.subst (X * c)

theorem main : ∀ n : ℕ, 4 ≤ n →
      ((n : ℚ)*((n : ℚ)-3)) * coeff n A +
        (2*(-4*(n : ℚ)^2+15*(n : ℚ)-10)) * coeff (n - 1) A +
        ((15*(n : ℚ)^2-69*(n : ℚ)+80)) * coeff (n - 2) A +
        (2*((n : ℚ)-2)*(2*(n : ℚ)-5)) * coeff (n - 3) A = 0 := by
  sorry

end OMA.S_oeis_a109263
