import Mathlib

/-!
# A057886: Number of integer 4-tuples that give the lengths of the sides of a nondegenerate quadrilateral with perimeter n.

Source: https://oeis.org/A057886

Conjectures from Colin Barker, Oct 27 2013:
  a(n) = ((n-1)*((n-2)*n+18)+6*sin((Pi*n)/2)+18*cos((Pi*n)/2))/96 for n even;
  a(n) = (n^3-7*n+6*sin((Pi*n)/2)+18*cos((Pi*n)/2))/96 for n odd.
  G.f.: x^4*(x^3-x^2+1) / ((x-1)^4*(x+1)^3*(x^2+1)).

Conventions:
* A quadrilateral with perimeter n is given by its four side lengths in cyclic order, a function
  f : Fin 4 → ℕ with positive values and sum n; it is nondegenerate when every side is shorter
  than the sum of the other three.
* As in the entry's example (a(8) = 5: (1,1,3,3), (1,2,2,3), (1,2,3,2), (1,3,1,3), (2,2,2,2)) and
  its Maple and Mathematica programs (dihedral necklaces), two 4-tuples describe the same
  quadrilateral when one is obtained from the other by a rotation or a reflection of the cyclic
  order: g(i) = f(i + r) for all i, or g(i) = f(r - i) for all i, for some r (indices mod 4).
  This relation is an equivalence, and `a n` is the number of its classes, `Nat.card` of the
  quotient.
* Offset 1 (data 0, 0, 0, 1, 1, 2, 3, 5, 7, 9, ...); the definition gives a(0) = 0, so the g.f. is
  stated for the series with coefficient a(n) at X^n, as an identity of formal power series over
  ℚ with the denominator multiplied out. The closed forms are stated in ℝ for every n ≥ 1, with
  Pi = Real.pi.
-/

namespace OMA.S_oeis_a057886

/-- Side lengths, in cyclic order, of the nondegenerate quadrilaterals with perimeter n. -/
def Quad (n : ℕ) : Type :=
  {f : Fin 4 → ℕ // (∀ i, 0 < f i) ∧ ∑ i, f i = n ∧ ∀ i, f i < ∑ j ∈ Finset.univ.erase i, f j}

/-- Two tuples give the same quadrilateral (rotation or reflection of the cyclic order). -/
def SameQuad (n : ℕ) (f g : Quad n) : Prop :=
  ∃ r : Fin 4, (∀ i, g.1 i = f.1 (i + r)) ∨ (∀ i, g.1 i = f.1 (r - i))

/-- A057886(n). -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (Quot (SameQuad n))

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℝ) = (((n : ℝ) - 1) * (((n : ℝ) - 2) * n + 18) +
      6 * Real.sin (Real.pi * n / 2) + 18 * Real.cos (Real.pi * n / 2)) / 96) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℝ) = ((n : ℝ) ^ 3 - 7 * n +
      6 * Real.sin (Real.pi * n / 2) + 18 * Real.cos (Real.pi * n / 2)) / 96) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) ^ 4 * (X + 1) ^ 3 * (X ^ 2 + 1) : PowerSeries ℚ) =
      X ^ 4 * (X ^ 3 - X ^ 2 + 1)) := by
  sorry

end OMA.S_oeis_a057886
