import Mathlib

/-!
# A224013: Number of 3 X n 0..2 arrays with rows nondecreasing and antidiagonals unimodal

Source: https://oeis.org/A224013
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Mar 30 2013; g.f. and recurrence conjectured by
Colin Barker, Aug 26 2018).

R. H. Hardin's sequence (offset 1, data 27, 216, 868, 2661, 6815, 15340, ...). An array x(i,j) with rows i = 0..2 and
columns j = 0..n-1 is given by its columns: x : Fin n → Fin 3 → Fin 3, where x j i is the entry in row i and
column j (value in 0..2). Rows are nondecreasing: x(i,j) ≤ x(i,j+1).
An antidiagonal consists of the cells (i,j) with i+j constant; it has at most three cells, namely
x(2,j), x(1,j+1), x(0,j+2), and a sequence of at most two elements is always unimodal, so the antidiagonals
are unimodal exactly when no middle element is smaller than both of its neighbors on the antidiagonal.

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (23/360)*n^6 + (27/40)*n^5 + (271/72)*n^4 + (65/8)*n^3 + (2101/180)*n^2 + (97/10)*n - 1 for n > 1 (over ℚ);
G.f.: x*(27 + 27*x - 77*x^2 + 176*x^3 - 199*x^4 + 129*x^5 - 43*x^6 + 6*x^7) / (1 - x)^7 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n > 8.
-/

namespace OMA.S_oeis_a224013

/-- Consecutive columns u (column j), v (column j+1): rows are nondecreasing. -/
def BlockOK (u v : Fin 3 → Fin 3) : Prop :=
  ∀ i : Fin 3, u i ≤ v i

/-- Three consecutive columns u, v, w (columns j, j+1, j+2): the antidiagonal x(2,j), x(1,j+1), x(0,j+2)
is unimodal. -/
def TriOK (u v w : Fin 3 → Fin 3) : Prop :=
  ¬ (v 1 < u 2 ∧ v 1 < w 0)

/-- The array conditions: rows nondecreasing, antidiagonals unimodal. -/
def Good {L : ℕ} (x : Fin L → Fin 3 → Fin 3) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j)) ∧
    (∀ i j l : Fin L, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TriOK (x i) (x j) (x l))

/-- a(n): the number of such 3 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 3 → Fin 3 // Good x}

/-- The conjectured g.f. x*(27 + 27*x - 77*x^2 + 176*x^3 - 199*x^4 + 129*x^5 - 43*x^6 + 6*x^7) / (1 - x)^7. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (27 + 27 * PowerSeries.X - 77 * PowerSeries.X ^ 2 + 176 * PowerSeries.X ^ 3 - 199 * PowerSeries.X ^ 4 + 129 * PowerSeries.X ^ 5 - 43 * PowerSeries.X ^ 6 + 6 * PowerSeries.X ^ 7)) * ((1 - PowerSeries.X) ^ 7)⁻¹

/-- The recurrence (n > 8), the g.f. and the empirical closed form (n > 1). -/
theorem main :
    (∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 21 * (a (n - 2) : ℤ) + 35 * (a (n - 3) : ℤ) - 35 * (a (n - 4) : ℤ) + 21 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) + (a (n - 7) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (23 / 360) * (n : ℚ) ^ 6 + (27 / 40) * (n : ℚ) ^ 5 + (271 / 72) * (n : ℚ) ^ 4 + (65 / 8) * (n : ℚ) ^ 3 + (2101 / 180) * (n : ℚ) ^ 2 + (97 / 10) * (n : ℚ) - 1) := by
  sorry

end OMA.S_oeis_a224013
