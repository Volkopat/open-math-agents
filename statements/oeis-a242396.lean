import Mathlib

/-!
# A242396: Number of rows of equilateral triangles (sides length = 1) that intersect the circumference of a circle of radius n centered at (0,0) or (1/2,0)

Source: https://oeis.org/A242396
Credit: @sobrien032

The tiling of the plane by equilateral triangles of side 1, with horizontal sides and a vertex at
the origin, has its rows as the horizontal strips between consecutive lines `y = j * (√3/2)`,
`j ∈ ℤ`. Row `k` is the closed strip `k * (√3/2) ≤ y ≤ (k + 1) * (√3/2)`. Both centers named in
the entry, (0,0) and (1/2,0), lie on the line `y = 0`, and whether a row meets the circle depends
only on the `y`-coordinates, so the two centers give the same count; the circle below is
centered at the origin. a(n), `n ≥ 1`, is the number of rows that meet the circle of radius `n`.
This gives the listed terms 4, 6, 8, 10, 12, 14, 18, 20, ... (the entry's program computes
the same values).

Conjecture (Ralf Stephan, May 18 2014): "G.f., conjectured: (-2*x^14 + 4*x^13 + 2*x^12 + 2*x^11
+ 2*x^10 + 2*x^9 + 2*x^8 + 4*x^7 + 2*x^6 + 2*x^5 + 2*x^4 + 2*x^3 + 2*x^2 + 4*x)/(x^14 - x^13
- x + 1)."
With offset 1 the g.f. is the series `Σ_{n ≥ 1} a(n) x^n`, written `X * mk (fun n => a (n + 1))`;
the claim is stated as an identity of formal power series over `ℚ` after multiplying by the
denominator.
-/

namespace OMA.S_oeis_a242396

/-- Row `k` of the tiling meets the circle of radius `n` centered at the origin. -/
def RowMeetsCircle (n : ℕ) (k : ℤ) : Prop :=
  ∃ x y : ℝ, x ^ 2 + y ^ 2 = (n : ℝ) ^ 2 ∧
    (k : ℝ) * (Real.sqrt 3 / 2) ≤ y ∧ y ≤ ((k : ℝ) + 1) * (Real.sqrt 3 / 2)

/-- A242396(n): the number of rows that meet the circle of radius `n` (a finite set). -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {k : ℤ // RowMeetsCircle n k}

open PowerSeries in
/-- Stephan's conjectured g.f., cleared of its denominator. -/
theorem main :
    X * mk (fun n => (a (n + 1) : ℚ)) * (X ^ 14 - X ^ 13 - X + 1) =
      -2 * X ^ 14 + 4 * X ^ 13 + 2 * X ^ 12 + 2 * X ^ 11 + 2 * X ^ 10 + 2 * X ^ 9 + 2 * X ^ 8 +
        4 * X ^ 7 + 2 * X ^ 6 + 2 * X ^ 5 + 2 * X ^ 4 + 2 * X ^ 3 + 2 * X ^ 2 + 4 * X := by
  sorry

end OMA.S_oeis_a242396
