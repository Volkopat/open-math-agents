import Mathlib

/-!
# A223322: Rolling icosahedron footprints: number of 2 X n 0..11 arrays starting with 0 where 0..11 label vertices of an icosahedron and every array movement to a horizontal or antidiagonal neighbor moves along an icosahedral edge

Source: https://oeis.org/A223322
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 12, 125, 1625, 21125, 274625, ...). An array is a map
x : Fin 2 → Fin n → Fin 12 (row i, column j, vertex label in 0..11), with x(0,0) = 0. The vertex
neighbours are those listed in the entry's example:
0 -> 1 2 5 6 7, 1 -> 0 2 3 7 8, 2 -> 0 1 4 6 8, 3 -> 1 7 8 9 11, 4 -> 2 6 8 9 10, 5 -> 0 6 7 10 11,
6 -> 0 2 4 5 10, 7 -> 0 1 3 5 11, 8 -> 1 2 3 4 9, 9 -> 3 4 8 10 11, 10 -> 4 5 6 9 11,
11 -> 3 5 7 9 10.
Cells (i,j), (i',j') are horizontal neighbours when i = i' and |j - j'| = 1, and antidiagonal
neighbours when |i - i'| = 1 and i + j = i' + j' (so (i,j) and (i+1,j-1)); moving between such
neighbours must follow an icosahedral edge. (Vertical and diagonal neighbours are not constrained.)

Conjectures (Colin Barker, Aug 19 2018), together with the empirical recurrence of the entry:
a(n) = 13*a(n-1) for n>2;
G.f.: x*(12 - 31*x) / (1 - 13*x) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 125*13^(n-2) for n>1.
-/

namespace OMA.S_oeis_a223322

/-- The neighbours of each vertex of the icosahedron, as listed in the entry. -/
def nbrs : Fin 12 → List (Fin 12) :=
  ![[1, 2, 5, 6, 7], [0, 2, 3, 7, 8], [0, 1, 4, 6, 8], [1, 7, 8, 9, 11], [2, 6, 8, 9, 10],
    [0, 6, 7, 10, 11], [0, 2, 4, 5, 10], [0, 1, 3, 5, 11], [1, 2, 3, 4, 9], [3, 4, 8, 10, 11],
    [4, 5, 6, 9, 11], [3, 5, 7, 9, 10]]

/-- u and v are joined by an icosahedral edge. -/
def edge (u v : Fin 12) : Prop := v ∈ nbrs u

/-- Cells p, q of a 2 X n array are horizontal or antidiagonal neighbours. -/
def Adj {n : ℕ} (p q : Fin 2 × Fin n) : Prop :=
  (p.1 = q.1 ∧ ((p.2 : ℕ) = q.2 + 1 ∨ (q.2 : ℕ) = p.2 + 1)) ∨
    ((p.1 : ℕ) + p.2 = q.1 + q.2 ∧ ((p.1 : ℕ) = q.1 + 1 ∨ (q.1 : ℕ) = p.1 + 1))

/-- Every such movement follows an edge, and the array starts with 0. -/
def Good {n : ℕ} (x : Fin 2 → Fin n → Fin 12) : Prop :=
  (∀ p q : Fin 2 × Fin n, Adj p q → edge (x p.1 p.2) (x q.1 q.2)) ∧
    ∀ h : 0 < n, x 0 ⟨0, h⟩ = 0

/-- a(n): the number of such 2 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin 2 → Fin n → Fin 12 // Good x}

/-- The conjectured g.f. x*(12 - 31*x) / (1 - 13*x). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (12 - 31 * PowerSeries.X)) * (1 - 13 * PowerSeries.X)⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 2 < n → a n = 13 * a (n - 1)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 < n → a n = 125 * 13 ^ (n - 2)) := by
  sorry

end OMA.S_oeis_a223322
