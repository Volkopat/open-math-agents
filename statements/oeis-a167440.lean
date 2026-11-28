import Mathlib

/-!
# A167440: 5th GegenbauerC polynomial evaluated at powers of 2 (multiplied by 5)

Source: https://oeis.org/A167440
Credit: @ivillar

Vladimir Joseph Stephan Orlovsky's sequence (offset 1). The entry's program is
`Table[GegenbauerC[5,2^n],{n,0,30}]*5`, so a(n) = 5 * GegenbauerC[5, 2^(n-1)] for n ≥ 1, where
Mathematica's two-argument GegenbauerC[n, x] is the renormalized Gegenbauer polynomial
lim_{m→0} C_n^(m)(x)/m = (2/n) * T_n(x) (T_n = Chebyshev polynomial of the first kind,
Mathlib's `Polynomial.Chebyshev.T`). This reproduces the data 2, 724, 30248, 1028176, ...

Conjectures from Colin Barker, Oct 27 2014:
  a(n) = 2^n*(5-5*4^n+16^n).
  a(n) = 42*a(n-1)-336*a(n-2)+512*a(n-3).
  G.f.: -2*x*(256*x^2+320*x+1) / ((2*x-1)*(8*x-1)*(32*x-1)).
The values are computed in ℚ; the g.f. is that of Sum_{n ≥ 1} a(n) x^n.
-/

namespace OMA.S_oeis_a167440

open Polynomial

/-- Mathematica's GegenbauerC[n, x] (two arguments): the renormalized Gegenbauer polynomial
lim_{m→0} C_n^(m)(x)/m = (2/n) T_n(x) for n ≥ 1, with T_n the Chebyshev polynomial of the first
kind. -/
noncomputable def gegenbauerC (n : ℕ) (x : ℚ) : ℚ := 2 / n * (Chebyshev.T ℚ n).eval x

/-- a(n) = 5 * GegenbauerC[5, 2^(n-1)] (offset 1), as in the Mathematica program of the entry. -/
noncomputable def a (n : ℕ) : ℚ := 5 * gegenbauerC 5 (2 ^ (n - 1))

/-- The conjectured g.f. -2*x*(256*x^2+320*x+1) / ((2*x-1)*(8*x-1)*(32*x-1)) over ℚ. -/
noncomputable def G : PowerSeries ℚ :=
  (-2 * PowerSeries.X * (256 * PowerSeries.X ^ 2 + 320 * PowerSeries.X + 1)) *
    ((2 * PowerSeries.X - 1) * (8 * PowerSeries.X - 1) * (32 * PowerSeries.X - 1))⁻¹

/-- Barker's conjectures: the closed form (n ≥ 1), the recurrence (n ≥ 4, so that every index is at
least 1) and the g.f. of Sum_{n ≥ 1} a(n) x^n. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 2 ^ n * (5 - 5 * 4 ^ n + 16 ^ n)) ∧
    (∀ n : ℕ, 4 ≤ n → a n = 42 * a (n - 1) - 336 * a (n - 2) + 512 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then 0 else a n) = G := by
  sorry

end OMA.S_oeis_a167440
