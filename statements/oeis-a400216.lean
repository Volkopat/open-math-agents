import Mathlib

/-!
# A400216: Scaled x-coordinates of the vertices of a Boerdijk-Coxeter helix starting at a tetrahedron with vertices (-1,-1,-1), (1, -1, 1), (-1, 1, 1), and (1, 1, -1).

Source: https://oeis.org/A400216
Credit: @agchua

In the formula section of A400216 (the entry is by Peter Kagey, Sep 21 2026):
  G.f.: (54*x^6 - 84*x^5 - 66*x^4 + 23*x^3 + 9*x^2 + x - 1)/((3*x - 1)^2 * (9*x^2 + 4*x + 1)) (conjectured).
Definition. In a Boerdijk-Coxeter helix with vertices v(0), v(1), v(2), ..., every four consecutive
vertices v(n), v(n+1), v(n+2), v(n+3) form a regular tetrahedron, and the next tetrahedron shares the
face v(n+1), v(n+2), v(n+3) with it, so v(n+4) is the mirror image of v(n) in the plane of that
face. In a regular tetrahedron the foot of the altitude from v(n) is the centroid of the opposite
face, hence v(n+4) = (2/3)*(v(n+1) + v(n+2) + v(n+3)) - v(n).
The first four vertices are taken in the order of the example section of the entry:
v(0) = (-1,-1,-1), v(1) = (-1,1,1), v(2) = (1,-1,1), v(3) = (1,1,-1). This fixes the helix (one of
the 24 choices described in the entry), and it gives the ten vertices listed there
(v(4) = (5/3,5/3,5/3), v(5) = (31/9,1/9,1/9), v(6) = (83/27,77/27,-13/27), ...).
By the comment of the entry, a(n) is the x-coordinate of v(n) scaled by k = 1 if n <= 3 and
k = 3^(n-3) otherwise: -1, -1, 1, 1, 5, 31, 83, 361, ... as listed (offset 0).
The g.f. is stated as an identity of formal power series over ℚ:
(∑ a(n) X^n) * ((3X - 1)^2 * (9X^2 + 4X + 1)) = 54X^6 - 84X^5 - 66X^4 + 23X^3 + 9X^2 + X - 1.
-/

namespace OMA.S_oeis_a400216

/-- The vertices v(n) of the helix, as points of ℚ^3 (coordinates 0, 1, 2 = x, y, z):
v(n+4) is the mirror image of v(n) in the plane of v(n+1), v(n+2), v(n+3). -/
def V : ℕ → Fin 3 → ℚ
  | 0 => ![-1, -1, -1]
  | 1 => ![-1, 1, 1]
  | 2 => ![1, -1, 1]
  | 3 => ![1, 1, -1]
  | (n + 4) => fun i => 2 / 3 * (V (n + 1) i + V (n + 2) i + V (n + 3) i) - V n i

/-- A400216(n): the x-coordinate of v(n), scaled by 1 if n <= 3 and by 3^(n-3) otherwise. -/
def a (n : ℕ) : ℚ := (if n ≤ 3 then 1 else (3 : ℚ) ^ (n - 3)) * V n 0

/-- The conjectured g.f. (54x^6 - 84x^5 - 66x^4 + 23x^3 + 9x^2 + x - 1)/((3x - 1)^2 (9x^2 + 4x + 1)). -/
theorem main : PowerSeries.mk a *
      ((3 * PowerSeries.X - 1) ^ 2 * (9 * PowerSeries.X ^ 2 + 4 * PowerSeries.X + 1)) =
    54 * PowerSeries.X ^ 6 - 84 * PowerSeries.X ^ 5 - 66 * PowerSeries.X ^ 4 +
      23 * PowerSeries.X ^ 3 + 9 * PowerSeries.X ^ 2 + PowerSeries.X - 1 := by
  sorry

end OMA.S_oeis_a400216
