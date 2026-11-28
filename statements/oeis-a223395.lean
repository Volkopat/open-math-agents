import Mathlib

/-!
# A223395: 4 X 4 square grid graph coloring a rectangular array: number of n X 1 0..15 arrays where 0..15 label nodes of the square grid graph and every array movement to a horizontal or vertical neighbor moves along an edge of this graph

Source: https://oeis.org/A223395
Credit: @ivillar

Status: open conjecture (empirical recurrence of R. H. Hardin, Mar 19 2013; g.f. and closed form conjectured by Colin Barker, Aug 20 2018); a proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 16, 48, 152, 488, 1576, 5096, ...). An array is a map
x : Fin n → Fin 1 → Fin 16 (row i, column j, value in 0..15).
The nodes 0..15 of the 4 X 4 square grid graph are numbered row by row (node k sits at row k/4,
column k mod 4), which gives the neighbor table of the entry (0 -> 1 4, 1 -> 0 2 5, ...,
5 -> 4 1 6 9, ..., 15 -> 14 11). An n X 1 array has only vertical neighbors, so the condition is that
consecutive entries x(i,0), x(i+1,0) are joined by an edge of the graph.

Conjectures of the entry:
* Empirical (Hardin): a(n) = 3*a(n-1) + 2*a(n-2) - 4*a(n-3) (stated for n ≥ 4, so that all indices
  are at least the offset 1; over ℤ);
* G.f. (Barker): 8*x*(2 - 3*x^2) / ((1 - x)*(1 - 2*x - 4*x^2)) (of Sum_{n ≥ 1} a(n) x^n, as a power
  series over ℚ);
* a(n) = (8 + (11-5*sqrt(5))*(1-sqrt(5))^n + (1+sqrt(5))^n*(11+5*sqrt(5))) / 5 (Barker; n ≥ 1,
  over ℝ).
-/

namespace OMA.S_oeis_a223395

/-- Nodes u, v of the 4 X 4 square grid graph (node k at row k / 4, column k % 4) are joined by an
edge: same row and adjacent columns, or same column and adjacent rows. -/
def Adj (u v : Fin 16) : Prop :=
  ((u : ℕ) / 4 = (v : ℕ) / 4 ∧ ((u : ℕ) % 4 + 1 = (v : ℕ) % 4 ∨ (v : ℕ) % 4 + 1 = (u : ℕ) % 4)) ∨
  ((u : ℕ) % 4 = (v : ℕ) % 4 ∧ ((u : ℕ) / 4 + 1 = (v : ℕ) / 4 ∨ (v : ℕ) / 4 + 1 = (u : ℕ) / 4))

/-- a(n): the number of n X 1 arrays with entries in 0..15 in which vertically adjacent entries are
joined by an edge of the graph. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 1 → Fin 16 //
    ∀ i : Fin n, ∀ h : (i : ℕ) + 1 < n, Adj (x i 0) (x ⟨(i : ℕ) + 1, h⟩ 0)}

/-- The conjectured g.f. 8*x*(2 - 3*x^2) / ((1 - x)*(1 - 2*x - 4*x^2)). -/
noncomputable def G : PowerSeries ℚ :=
  (8 * PowerSeries.X * (2 - 3 * PowerSeries.X ^ 2)) * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2))⁻¹

/-- The empirical recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) + 2 * a (n - 2) - 4 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (8 + (11 - 5 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ n + (1 + Real.sqrt 5) ^ n * (11 + 5 * Real.sqrt 5)) / 5) := by
  sorry

end OMA.S_oeis_a223395
