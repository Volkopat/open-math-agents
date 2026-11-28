import Mathlib

/-!
# A131498: For D_2 type groups as polyhedra: {F,V,E,dimension}->{n+2,2*n,3*n,2*n*(2*n-1)/2}

Source: https://oeis.org/A131498
Credit: @ivillar

The sequence (offset 1, as in the OEIS) lists, for m = 1, 2, 3, ..., the four numbers
F = m + 2, V = 2m, E = 3m and dimension = 2m(2m - 1)/2, in this order:
3, 2, 3, 1, 4, 4, 6, 6, 5, 6, 9, 15, ... The entry records Colin Barker's conjecture (Jan 03 2020)
G.f. x (3 + 2x + 3x^2 + x^3 - 5x^4 - 2x^5 - 3x^6 + 3x^7 + 2x^8) / ((1 - x)^3 (1 + x)^3 (1 + x^2)^3),
stated here with its denominator cleared and a(0) = 0 as the constant term.
-/

namespace OMA.S_oeis_a131498

open PowerSeries

/-- The quadruple {F, V, E, dimension} attached to `m`, with entries indexed by `0, 1, 2, 3`. -/
def quad (m r : ℕ) : ℕ :=
  if r = 0 then m + 2 else if r = 1 then 2 * m else if r = 2 then 3 * m
  else 2 * m * (2 * m - 1) / 2

/-- The n-th term for n ≥ 1 (offset 1), with `a 0 = 0`. -/
def a (n : ℕ) : ℕ := if n = 0 then 0 else quad ((n - 1) / 4 + 1) ((n - 1) % 4)

theorem main :
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 3) =
      X * (3 + 2 * X + 3 * X ^ 2 + X ^ 3 - 5 * X ^ 4 - 2 * X ^ 5 - 3 * X ^ 6 + 3 * X ^ 7 +
        2 * X ^ 8) := by
  sorry

end OMA.S_oeis_a131498
