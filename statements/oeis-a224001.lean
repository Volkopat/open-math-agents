import Mathlib

/-!
# A224001: Number of 3 X n 0..2 arrays with antidiagonals unimodal and rows and diagonals nondecreasing

Source: https://oeis.org/A224001
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Mar 30 2013; g.f. and recurrence conjectured by
Colin Barker, Aug 25 2018).

R. H. Hardin's sequence (offset 1, data 27, 157, 476, 1144, 2403, 4614, ...). An array x(i,j) with rows i = 0..2 and
columns j = 0..n-1 is given by its columns: x : Fin n → Fin 3 → Fin 3, where x j i is the entry in row i and
column j (value in 0..2). Rows are nondecreasing: x(i,j) ≤ x(i,j+1).
Diagonals are nondecreasing: x(i,j) ≤ x(i+1,j+1).
An antidiagonal consists of the cells (i,j) with i+j constant; it has at most three cells, namely
x(2,j), x(1,j+1), x(0,j+2), and a sequence of at most two elements is always unimodal, so the antidiagonals
are unimodal exactly when no middle element is smaller than both of its neighbors on the antidiagonal.

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (1/144)*n^6 + (5/48)*n^5 + (163/144)*n^4 + (85/16)*n^3 + (895/36)*n^2 - (65/12)*n + 3 for n > 2 (over ℚ);
G.f.: x*(27 - 32*x - 56*x^2 + 164*x^3 - 159*x^4 + 85*x^5 - 32*x^6 + 9*x^7 - x^8) / (1 - x)^7 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n > 9.
-/

namespace OMA.S_oeis_a224001

/-- Consecutive columns u (column j), v (column j+1): rows and diagonals are nondecreasing. -/
def BlockOK (u v : Fin 3 → Fin 3) : Prop :=
  (∀ i : Fin 3, u i ≤ v i) ∧ u 0 ≤ v 1 ∧ u 1 ≤ v 2

/-- Three consecutive columns u, v, w (columns j, j+1, j+2): the antidiagonal x(2,j), x(1,j+1), x(0,j+2)
is unimodal. -/
def TriOK (u v w : Fin 3 → Fin 3) : Prop :=
  ¬ (v 1 < u 2 ∧ v 1 < w 0)

/-- The array conditions: rows and diagonals nondecreasing, antidiagonals unimodal. -/
def Good {L : ℕ} (x : Fin L → Fin 3 → Fin 3) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j)) ∧
    (∀ i j l : Fin L, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TriOK (x i) (x j) (x l))

/-- a(n): the number of such 3 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 3 → Fin 3 // Good x}

/-- The conjectured g.f. x*(27 - 32*x - 56*x^2 + 164*x^3 - 159*x^4 + 85*x^5 - 32*x^6 + 9*x^7 - x^8) / (1 - x)^7. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (27 - 32 * PowerSeries.X - 56 * PowerSeries.X ^ 2 + 164 * PowerSeries.X ^ 3 - 159 * PowerSeries.X ^ 4 + 85 * PowerSeries.X ^ 5 - 32 * PowerSeries.X ^ 6 + 9 * PowerSeries.X ^ 7 - PowerSeries.X ^ 8)) * ((1 - PowerSeries.X) ^ 7)⁻¹

/-- The recurrence (n > 9), the g.f. and the empirical closed form (n > 2). -/
theorem main :
    (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 21 * (a (n - 2) : ℤ) + 35 * (a (n - 3) : ℤ) - 35 * (a (n - 4) : ℤ) + 21 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) + (a (n - 7) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = (1 / 144) * (n : ℚ) ^ 6 + (5 / 48) * (n : ℚ) ^ 5 + (163 / 144) * (n : ℚ) ^ 4 + (85 / 16) * (n : ℚ) ^ 3 + (895 / 36) * (n : ℚ) ^ 2 - (65 / 12) * (n : ℚ) + 3) := by
  sorry

end OMA.S_oeis_a224001
