import Mathlib

/-!
# A223270: Rolling cube footprints: number of 2 X n 0..5 arrays starting with 0 where 0..5 label faces of a cube and every array movement to a horizontal, diagonal or antidiagonal neighbor moves across a corresponding cube edge

Source: https://oeis.org/A223270
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 6, 48, 576, 6144, 67584, ...). An array is a map
x : Fin 2 → Fin n → Fin 6 (row i, column j, face label in 0..5), with x(0,0) = 0. The face neighbours
listed in the entry's example are 0 -> 1,2,3,4; 1 -> 0,2,3,5; 2 -> 0,1,4,5; 3 -> 0,1,4,5; so faces
u and v share an edge iff u ≠ v and u + v ≠ 5 (the opposite pairs are {0,5}, {1,4}, {2,3}). Cells
(i,j), (i',j') are horizontal, diagonal or antidiagonal neighbours when |i - i'| ≤ 1 and
|j - j'| = 1; moving between such neighbours must cross a cube edge, i.e. their labels must be
adjacent faces. (Vertical neighbours are not constrained.)

Conjectures (Colin Barker, Aug 18 2018), together with the empirical recurrence of the entry:
a(n) = 8*a(n-1) + 32*a(n-2) (stated for n ≥ 3, all indices at least the offset 1);
G.f.: 6*x / (1 - 8*x - 32*x^2) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (sqrt(3)*(-(4-4*sqrt(3))^n + (4*(1+sqrt(3)))^n)) / 4 (n ≥ 1, over ℝ).
-/

namespace OMA.S_oeis_a223270

/-- Faces u and v of the cube share an edge. -/
def adjFace (u v : Fin 6) : Prop := u ≠ v ∧ (u : ℕ) + v ≠ 5

/-- Cells p, q of a 2 X n array are horizontal, diagonal or antidiagonal neighbours. -/
def Adj {n : ℕ} (p q : Fin 2 × Fin n) : Prop :=
  (p.1 : ℕ) ≤ q.1 + 1 ∧ (q.1 : ℕ) ≤ p.1 + 1 ∧ ((p.2 : ℕ) = q.2 + 1 ∨ (q.2 : ℕ) = p.2 + 1)

/-- Every such movement crosses a cube edge, and the array starts with 0. -/
def Good {n : ℕ} (x : Fin 2 → Fin n → Fin 6) : Prop :=
  (∀ p q : Fin 2 × Fin n, Adj p q → adjFace (x p.1 p.2) (x q.1 q.2)) ∧
    ∀ h : 0 < n, x 0 ⟨0, h⟩ = 0

/-- a(n): the number of such 2 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin 2 → Fin n → Fin 6 // Good x}

/-- The conjectured g.f. 6*x / (1 - 8*x - 32*x^2). -/
noncomputable def G : PowerSeries ℚ :=
  (6 * PowerSeries.X) * (1 - 8 * PowerSeries.X - 32 * PowerSeries.X ^ 2)⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 8 * a (n - 1) + 32 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = Real.sqrt 3 *
      (-(4 - 4 * Real.sqrt 3) ^ n + (4 * (1 + Real.sqrt 3)) ^ n) / 4) := by
  sorry

end OMA.S_oeis_a223270
