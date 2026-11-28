import Mathlib

/-!
# A400217: Scaled y-coordinates of the vertices of a Boerdijk-Coxeter helix starting at a tetrahedron with vertices (-1,-1,-1), (1, -1, 1), (-1, 1, 1), and (1, 1, -1).

Source: https://oeis.org/A400217
Credit: @agchua

In the formula section of A400217 (entry by Peter Kagey, Sep 21 2026):
  G.f.: (-54*x^6 + 84*x^5 - 90*x^4 + 15*x^3 + 3*x^2 + 3*x - 1)/((3*x - 1)^2*(9*x^2 + 4*x + 1)) (conjectured).
Definition. In a Boerdijk-Coxeter helix v(0), v(1), v(2), ... every four consecutive vertices form a
regular tetrahedron and consecutive tetrahedra share a face, so v(n+4) is the reflection of v(n) in
the plane through v(n+1), v(n+2), v(n+3). In a regular tetrahedron the foot of the perpendicular from
a vertex to the opposite face is the centroid of that face, so this reflection is
v(n+4) = (2/3)(v(n+1) + v(n+2) + v(n+3)) - v(n), coordinate by coordinate. The order of the four
starting vertices along the helix is that of the example of the entry, (-1,-1,-1), (-1,1,1), (1,-1,1),
(1,1,-1); with it the rule gives the first ten vertices listed in the example and the listed terms
-1, 1, -1, 1, 5, 1, 77, 169, 413, ... (by the comment, this is the one of the 24 helices on this
tetrahedron that asymptotically maximizes the x-value and then the y-value). Coordinates are indexed
0, 1, 2 for x, y, z. By the comment, the coordinate of v(n) is scaled by k = 1 if n <= 3 and by
k = 3^(n-3) otherwise. Offset 0.
The g.f. is stated as an identity of formal power series over ℚ: (Sum a(n) X^n) times
(3X - 1)^2 (9X^2 + 4X + 1) equals -54X^6 + 84X^5 - 90X^4 + 15X^3 + 3X^2 + 3X - 1.
-/

namespace OMA.S_oeis_a400217

/-- The vertices of the helix: the starting tetrahedron in the order of the example, then
v(n+4) = (2/3)(v(n+1) + v(n+2) + v(n+3)) - v(n), the reflection of v(n) in the opposite face. -/
def v : ℕ → Fin 3 → ℚ
  | 0 => ![-1, -1, -1]
  | 1 => ![-1, 1, 1]
  | 2 => ![1, -1, 1]
  | 3 => ![1, 1, -1]
  | (n + 4) => fun i => 2 / 3 * (v (n + 1) i + v (n + 2) i + v (n + 3) i) - v n i

/-- A400217(n): the y-coordinate of v(n), scaled by 1 if n ≤ 3 and by 3^(n-3) otherwise. -/
def a (n : ℕ) : ℚ := (if n ≤ 3 then 1 else (3 : ℚ) ^ (n - 3)) * v n 1

/-- The conjectured g.f. (-54x^6+84x^5-90x^4+15x^3+3x^2+3x-1)/((3x-1)^2(9x^2+4x+1)). -/
theorem main :
    PowerSeries.mk a *
        ((3 * PowerSeries.X - 1) ^ 2 * (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) =
      -54 * PowerSeries.X ^ 6 + 84 * PowerSeries.X ^ 5 - 90 * PowerSeries.X ^ 4 +
        15 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 + 3 * PowerSeries.X - 1 := by
  sorry

end OMA.S_oeis_a400217
