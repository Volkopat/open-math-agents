import Mathlib

/-!
# A400218: Scaled z-coordinates of the vertices of a Boerdijk-Coxeter helix starting at a tetrahedron with vertices (-1,-1,-1), (1, -1, 1), (-1, 1, 1), and (1, 1, -1).

Source: https://oeis.org/A400218
Credit: @agchua

In the formula section of A400218 (entry by Peter Kagey, Sep 21 2026):
  G.f.: (18*x^5 + 26*x^4 - 24*x^3 - 5*x^2 + 1)/(27*x^3 + 3*x^2 - x - 1) (conjectured).
This file states the g.f. as an identity of formal power series over ℚ,
(∑ a(n) X^n) * (27X^3 + 3X^2 - X - 1) = 18X^5 + 26X^4 - 24X^3 - 5X^2 + 1.
The sequence has offset 0. The helix is the chain of regular tetrahedra v(n), v(n+1), v(n+2), v(n+3)
in which each tetrahedron is the mirror image of the previous one in their common face, so v(n+4) is
the reflection of v(n) in the plane of v(n+1), v(n+2), v(n+3). In a regular tetrahedron the foot of
the altitude from a vertex is the centroid of the opposite face, so that reflection is
v(n+4) = (2/3) (v(n+1) + v(n+2) + v(n+3)) - v(n); this is the rule used below. The four starting
vertices are taken in the order of the entry's example (the first ten vertices listed there):
v(0) = (-1,-1,-1), v(1) = (-1,1,1), v(2) = (1,-1,1), v(3) = (1,1,-1); the next ones are
(5/3, 5/3, 5/3), (31/9, 1/9, 1/9), (83/27, 77/27, -13/27), ... as listed. By the entry's comment,
a(n) is the z-coordinate of v(n) times k, with k = 1 for n ≤ 3 and k = 3^(n-3) otherwise.
-/

namespace OMA.S_oeis_a400218

/-- The reflection of the vertex p of a regular tetrahedron p q r s in the plane of the opposite
face q r s: twice the centroid of q, r, s minus p, coordinatewise. -/
def step (p q r s : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ :=
  (2 / 3 * (q.1 + r.1 + s.1) - p.1, 2 / 3 * (q.2.1 + r.2.1 + s.2.1) - p.2.1,
    2 / 3 * (q.2.2 + r.2.2 + s.2.2) - p.2.2)

/-- The vertices v(0), v(1), ... of the Boerdijk-Coxeter helix of A400218. -/
def v : ℕ → ℚ × ℚ × ℚ
  | 0 => (-1, -1, -1)
  | 1 => (-1, 1, 1)
  | 2 => (1, -1, 1)
  | 3 => (1, 1, -1)
  | (n + 4) => step (v n) (v (n + 1)) (v (n + 2)) (v (n + 3))

/-- A400218(n): the z-coordinate of v(n), scaled by 1 for n ≤ 3 and by 3^(n-3) for n > 3. -/
def a (n : ℕ) : ℚ := (if n ≤ 3 then 1 else 3 ^ (n - 3)) * (v n).2.2

/-- The conjectured g.f. (18x^5 + 26x^4 - 24x^3 - 5x^2 + 1)/(27x^3 + 3x^2 - x - 1). -/
theorem main : PowerSeries.mk a *
    (27 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 - PowerSeries.X - 1) =
    18 * PowerSeries.X ^ 5 + 26 * PowerSeries.X ^ 4 - 24 * PowerSeries.X ^ 3 -
      5 * PowerSeries.X ^ 2 + 1 := by
  sorry

end OMA.S_oeis_a400218
