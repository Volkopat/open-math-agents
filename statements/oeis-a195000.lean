import Mathlib

/-!
# OEIS A195000: Barker's conjectures

Source: https://oeis.org/A195000 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A195000 (R. H. Hardin, Sep 07 2011), offset 1: Number of lower triangles of a 4 X 4 0..n array with each element differing from all of its horizontal and vertical neighbors by one.
Formula section:
Conjectures from Colin Barker, May 06 2018: (Start)
G.f.: 2*x*(1 + 38*x + 45*x^2 + 21*x^3 + 2*x^4 + x^5) / (1 - x)^2.
a(n) = 24*(9*n - 17) for n>4.
a(n) = 2*a(n-1) - a(n-2) for n>6.
(End)

Formalization notes:
* The lower triangle of a 4 X 4 array is the set of cells (i, j) with j ≤ i (row i,
  column j, both in 0..3); an array assigns a value in 0..n to each cell.
* Horizontal and vertical neighbors: cells at distance one in one coordinate and equal in
  the other; "differing by one" is |x p - x q| = 1.
* The statement is Barker's conjectures, the problem as stated on lefttosolve.com: the
  generating function, the closed form and the recurrence.
* The definition gives a(0) = 0 (all values equal), so the generating function is
  A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^2 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 2, 80, 248, 458, 672, 888, 1104, 1320, 1536, 1752, 1968, 2184 for n = 1..12,
  the entry's first terms.
-/

namespace OMA.S_oeis_a195000

open Finset

/-- Two cells (i, j), j ≤ i, of the lower triangle of a 4 X 4 array are horizontal or
vertical neighbors. -/
def Nbr (p q : {p : Fin 4 × Fin 4 // p.2 ≤ p.1}) : Prop :=
  ((p.1.1 : ℤ) - q.1.1).natAbs + ((p.1.2 : ℤ) - q.1.2).natAbs = 1

/-- Each element differs from all of its horizontal and vertical neighbors by one. -/
def Good {n : ℕ} (x : {p : Fin 4 × Fin 4 // p.2 ≤ p.1} → Fin (n + 1)) : Prop :=
  ∀ p q, Nbr p q → ((x p : ℤ) - x q).natAbs = 1

/-- A195000(n): the lower triangles of a 4 X 4 array with entries in 0..n with
each element differing from all of its horizontal and vertical neighbors by one. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : {p : Fin 4 × Fin 4 // p.2 ≤ p.1} → Fin (n + 1) // Good x}

/-- The problem as the site states it. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 2 = 2 * PowerSeries.X * (1 + 38 * PowerSeries.X + 45 * PowerSeries.X ^ 2 + 21 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 24 * (9 * n - 17)) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) := by
  sorry

end OMA.S_oeis_a195000
