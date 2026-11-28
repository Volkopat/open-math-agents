import Mathlib

/-!
# Distances to a cyclic polygon and its tangent lines

The circumcircle has unit radius and center (0,0). Angles t(i) occur in
counterclockwise order, with t(i+n)=t(i)+2π. The point P is given by weights
on the vertices that are nonnegative and sum to one, which covers the
whole closed polygon. The tangent line at angle a has outward unit normal
(cos a,sin a) and supporting value 1. The chord between angles a and b has
outward normal at angle (a+b)/2 and supporting value cos((b-a)/2).
Subtracting the projection of P gives the perpendicular distances to those
lines. Multiplying the original inequality by cos(π/n) gives the form below.

Source: https://mathoverflow.net/questions/244984 (CC BY-SA)
Credit: @connoranderson
-/

namespace OMA.S_mo_244984
open Real Finset

noncomputable def vertex (a : ℝ) : ℝ × ℝ := (cos a,sin a)
noncomputable def projection (a : ℝ) (P : ℝ × ℝ) : ℝ := P.1*cos a + P.2*sin a

noncomputable def tangentDist (a : ℝ) (P : ℝ × ℝ) : ℝ :=
  1-projection a P

noncomputable def chordDist (a b : ℝ) (P : ℝ × ℝ) : ℝ :=
  cos ((b-a)/2)-projection ((a+b)/2) P

noncomputable def point (n : ℕ) (t w : ℕ → ℝ) : ℝ × ℝ :=
  (∑ i ∈ range n,w i * cos (t i),∑ i ∈ range n,w i * sin (t i))

theorem main : ∀ (n : ℕ) (t w : ℕ → ℝ), 3 ≤ n → StrictMono t →
    (∀ i, t (i+n)=t i+2*π) → (∀ i < n, 0 ≤ w i) → (∑ i ∈ range n,w i)=1 →
    let P := point n t w
    let d := ∑ i ∈ range n,chordDist (t i) (t (i+1)) P
    let D := ∑ i ∈ range n,tangentDist (t i) P
    d ≤ cos (π/n)*D ∧
      ((∀ i, t (i+1)=t i+2*π/n) → d=cos (π/n)*D) := by
  sorry

end OMA.S_mo_244984
