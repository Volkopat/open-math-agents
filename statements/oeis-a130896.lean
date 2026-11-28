import Mathlib

/-!
# A130896: For D_n type groups as polyhedra that are pyramid-like: {F,V,E,dimension}

Source: https://oeis.org/A130896
Credit: @ivillar

The sequence (offset 1, as in the OEIS) lists, for m = 1, 2, 3, ..., the four numbers
F = 2m + 1, V = 2m + 1, E = 4m and dimension = (2m + 1)((2m + 1) - 1)/2, in this order:
3, 3, 4, 3, 5, 5, 8, 10, 7, 7, 12, 21, ... The entry records Colin Barker's conjectures
(Jan 02 2020): G.f. x (3 + 3x + 4x^2 + 3x^3 - 4x^4 - 4x^5 - 4x^6 + x^7 + x^8 + x^9) /
((1 - x)^3 (1 + x)^3 (1 + x^2)^3) and a(n) = 3 a(n-4) - 3 a(n-8) + a(n-12) for n > 12.
The generating function is stated with its denominator cleared and a(0) = 0 as constant term.
-/

namespace OMA.S_oeis_a130896

open PowerSeries

/-- The quadruple {F, V, E, dimension} attached to `m`, with entries indexed by `0, 1, 2, 3`. -/
def quad (m r : ℕ) : ℕ :=
  if r = 0 then 2 * m + 1 else if r = 1 then 2 * m + 1 else if r = 2 then 4 * m
  else (2 * m + 1) * ((2 * m + 1) - 1) / 2

/-- The n-th term for n ≥ 1 (offset 1), with `a 0 = 0`. -/
def a (n : ℕ) : ℕ := if n = 0 then 0 else quad ((n - 1) / 4 + 1) ((n - 1) % 4)

theorem main :
    (mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 3) =
      X * (3 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 - 4 * X ^ 5 - 4 * X ^ 6 + X ^ 7 +
        X ^ 8 + X ^ 9)) ∧
    (∀ n : ℕ, 12 < n → (a n : ℤ) = 3 * a (n - 4) - 3 * a (n - 8) + a (n - 12)) := by
  sorry

end OMA.S_oeis_a130896
