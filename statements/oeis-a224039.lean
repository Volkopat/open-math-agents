import Mathlib

/-!
# A224039: Number of 3 X n 0..1 arrays with antidiagonals unimodal and rows and diagonals nondecreasing

Source: https://oeis.org/A224039
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Mar 30 2013; g.f. and recurrence conjectured by
Colin Barker, Aug 26 2018).

R. H. Hardin's sequence (offset 1, data 8, 21, 37, 58, 85, 119, ...). An array x(i,j) with rows i = 0..2 and
columns j = 0..n-1 is given by its columns: x : Fin n → Fin 3 → Fin 2, where x j i is the entry in row i and
column j (value in 0..1). Rows are nondecreasing: x(i,j) ≤ x(i,j+1).
Diagonals are nondecreasing: x(i,j) ≤ x(i+1,j+1).
An antidiagonal consists of the cells (i,j) with i+j constant; it has at most three cells, namely
x(2,j), x(1,j+1), x(0,j+2), and a sequence of at most two elements is always unimodal, so the antidiagonals
are unimodal exactly when no middle element is smaller than both of its neighbors on the antidiagonal.

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (1/6)*n^3 + 1*n^2 + (47/6)*n for n > 1 (over ℚ);
G.f.: x*(8 - 11*x + x^2 + 4*x^3 - x^4) / (1 - x)^4 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n > 5.
-/

namespace OMA.S_oeis_a224039

/-- Consecutive columns u (column j), v (column j+1): rows and diagonals are nondecreasing. -/
def BlockOK (u v : Fin 3 → Fin 2) : Prop :=
  (∀ i : Fin 3, u i ≤ v i) ∧ u 0 ≤ v 1 ∧ u 1 ≤ v 2

/-- Three consecutive columns u, v, w (columns j, j+1, j+2): the antidiagonal x(2,j), x(1,j+1), x(0,j+2)
is unimodal. -/
def TriOK (u v w : Fin 3 → Fin 2) : Prop :=
  ¬ (v 1 < u 2 ∧ v 1 < w 0)

/-- The array conditions: rows and diagonals nondecreasing, antidiagonals unimodal. -/
def Good {L : ℕ} (x : Fin L → Fin 3 → Fin 2) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j)) ∧
    (∀ i j l : Fin L, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TriOK (x i) (x j) (x l))

/-- a(n): the number of such 3 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 3 → Fin 2 // Good x}

/-- The conjectured g.f. x*(8 - 11*x + x^2 + 4*x^3 - x^4) / (1 - x)^4. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (8 - 11 * PowerSeries.X + PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4)) * ((1 - PowerSeries.X) ^ 4)⁻¹

/-- The recurrence (n > 5), the g.f. and the empirical closed form (n > 1). -/
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 6 * (a (n - 2) : ℤ) + 4 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (1 / 6) * (n : ℚ) ^ 3 + 1 * (n : ℚ) ^ 2 + (47 / 6) * (n : ℚ)) := by
  sorry

end OMA.S_oeis_a224039
