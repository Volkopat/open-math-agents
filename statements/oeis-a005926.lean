import Mathlib

/-!
# A005926: Theta series of diamond with respect to midpoint of edge.

Source: https://oeis.org/A005926
Credit: @eltociear

Conjecture (Vaclav Kotesovec, Nov 26 2026): Sum_{k=1..n} a(k) ~ Pi*n^(3/2)/48.

Conventions. The diamond structure is taken in the standard coordinates of Sloane
(J. Math. Phys. 28 (1987), 1653-1657): the union of the face-centred cubic lattice
D₃ = {v ∈ ℤ³ : v₁ + v₂ + v₃ even} and its translate D₃ + (1/2, 1/2, 1/2). The bond (edge)
from 0 to (1/2, 1/2, 1/2) has midpoint m = (1/4, 1/4, 1/4). The OEIS g.f. is
Sum_n a(n) q^(n/16) (see the %e line: 2*q^(3/16) + 6*q^(19/16) + ...), so
a(n) = #{x ∈ diamond : 16 * |x - m|² = n}.

This definition was checked against the OEIS b-file for all n = 0..10000 (all terms agree),
and the partial-sum ratio to Pi*n^(3/2)/48 is ≈ 1.0004 at n = 10000.

"~" is read as asymptotic equivalence as n → ∞ (`Asymptotics.IsEquivalent`).
-/

namespace OMA.S_oeis_a005926

/-- The diamond structure: D₃ ∪ (D₃ + (1/2, 1/2, 1/2)), with D₃ the integer vectors of even
coordinate sum. -/
def diamond : Set (Fin 3 → ℝ) :=
  {x | ∃ v : Fin 3 → ℤ, Even (∑ i, v i) ∧
    ((∀ i, x i = (v i : ℝ)) ∨ (∀ i, x i = (v i : ℝ) + 1 / 2))}

/-- The midpoint (1/4, 1/4, 1/4) of the edge from 0 to (1/2, 1/2, 1/2). -/
noncomputable def edgeMidpoint : Fin 3 → ℝ := fun _ => 1 / 4

/-- Squared Euclidean distance in ℝ³. -/
noncomputable def sqDist (x y : Fin 3 → ℝ) : ℝ := ∑ i, (x i - y i) ^ 2

/-- A005926: a(n) is the number of points of the diamond structure at squared distance
n/16 from the midpoint of an edge (the coefficient of q^(n/16) in the theta series). -/
noncomputable def a (n : ℕ) : ℕ :=
  {x : Fin 3 → ℝ | x ∈ diamond ∧ 16 * sqDist x edgeMidpoint = n}.ncard

theorem main :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (a k : ℝ))
      (fun n : ℕ => Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) / 48) := by
  sorry

end OMA.S_oeis_a005926
