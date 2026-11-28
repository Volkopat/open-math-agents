import Mathlib

/-!
# A223240: 3-loop graph coloring a rectangular array: number of n X 1 0..6 arrays where 0..6 label nodes of a graph with edges 0,1 1,2 2,0 0,3 3,4 4,0 0,5 5,6 6,0 and every array movement to a horizontal or vertical neighbor moves along an edge of this graph

Source: https://oeis.org/A223240
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 7, 18, 60, 168, 528, 1536, 4704, ...). An array is a map
x : Fin n → Fin 1 → Fin 7 (row i, column j, node label in 0..6). Cells (i,j), (i',j') are horizontal
or vertical neighbours when they agree in one coordinate and differ by 1 in the other; moving between
neighbours must follow an edge of the graph with edges {0,1}, {1,2}, {2,0}, {0,3}, {3,4}, {4,0},
{0,5}, {5,6}, {6,0}.

Conjectures (Colin Barker, Aug 17 2018), together with the empirical recurrence of the entry:
a(n) = a(n-1) + 6*a(n-2) (stated for n ≥ 3, all indices at least the offset 1);
G.f.: x*(7 + 11*x) / ((1 + 2*x)*(1 - 3*x)) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (64*3^n - 9*(-2)^n) / 30 (n ≥ 1, over ℚ).
-/

namespace OMA.S_oeis_a223240

/-- The edges of the 3-loop graph. -/
def edges : List (Fin 7 × Fin 7) :=
  [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0), (0, 5), (5, 6), (6, 0)]

/-- u and v are joined by an edge. -/
def edge (u v : Fin 7) : Prop := (u, v) ∈ edges ∨ (v, u) ∈ edges

/-- Cells p, q of an n X 1 array are horizontal or vertical neighbours. -/
def Nbr {n : ℕ} (p q : Fin n × Fin 1) : Prop :=
  ((p.1 : ℕ) = q.1 ∧ ((p.2 : ℕ) = q.2 + 1 ∨ (q.2 : ℕ) = p.2 + 1)) ∨
    ((p.2 : ℕ) = q.2 ∧ ((p.1 : ℕ) = q.1 + 1 ∨ (q.1 : ℕ) = p.1 + 1))

/-- Every movement to a horizontal or vertical neighbour moves along an edge. -/
def Good {n : ℕ} (x : Fin n → Fin 1 → Fin 7) : Prop :=
  ∀ p q : Fin n × Fin 1, Nbr p q → edge (x p.1 p.2) (x q.1 q.2)

/-- a(n): the number of such n X 1 arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin n → Fin 1 → Fin 7 // Good x}

/-- The conjectured g.f. x*(7 + 11*x) / ((1 + 2*x)*(1 - 3*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (7 + 11 * PowerSeries.X)) * ((1 + 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = a (n - 1) + 6 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (64 * 3 ^ n - 9 * (-2) ^ n) / 30) := by
  sorry

end OMA.S_oeis_a223240
