import Mathlib

/-!
# A224168: Number of n X 3 0..3 arrays with rows, diagonals and antidiagonals unimodal and columns nondecreasing

Source: https://oeis.org/A224168
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Mar 31 2013; g.f. and recurrence conjectured by
Colin Barker, Aug 28 2018).

R. H. Hardin's sequence (offset 1, data 50, 684, 4739, 22988, 87878, 282372, ...). An array is a map
x : Fin n → Fin 3 → Fin 4 (row i, column j, value in 0..3). A row is unimodal when it is nondecreasing up
to some position k and nonincreasing from k on. Columns are nondecreasing: x(i,j) ≤ x(i+1,j).
An antidiagonal consists of the cells (i,j) with i+j constant; it has at most three cells, namely
x(i,2), x(i+1,1), x(i+2,0), and a sequence of at most two elements is always unimodal, so the antidiagonals
are unimodal exactly when no middle element is smaller than both of its neighbors on the antidiagonal.
The same holds for the diagonals, with cells x(i,0), x(i+1,1), x(i+2,2).

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (353/181440)*n^9 + (17/560)*n^8 + (9083/30240)*n^7 + (1039/720)*n^6 + (46769/8640)*n^5 + (3863/360)*n^4 + (411149/22680)*n^3 + (14863/1260)*n^2 + (6497/1260)*n - 3 (n ≥ 1, over ℚ);
G.f.: x*(50 + 184*x + 149*x^2 + 378*x^3 - 327*x^4 + 412*x^5 - 228*x^6 + 107*x^7 - 22*x^8 + 3*x^9) / (1 - x)^10 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n > 10.
-/

namespace OMA.S_oeis_a224168

/-- A row is unimodal: nondecreasing up to some position k, nonincreasing from k on. -/
def LineOK (u : Fin 3 → Fin 4) : Prop :=
  ∃ k : Fin 3, (∀ i j : Fin 3, i ≤ j → j ≤ k → u i ≤ u j) ∧ (∀ i j : Fin 3, k ≤ i → i ≤ j → u j ≤ u i)

/-- Consecutive rows u (row i), v (row i+1): columns are nondecreasing. -/
def BlockOK (u v : Fin 3 → Fin 4) : Prop :=
  ∀ j : Fin 3, u j ≤ v j

/-- Three consecutive rows u, v, w (rows i, i+1, i+2): the antidiagonal x(i,2), x(i+1,1), x(i+2,0) and the
diagonal x(i,0), x(i+1,1), x(i+2,2) are unimodal. -/
def TriOK (u v w : Fin 3 → Fin 4) : Prop :=
  ¬ (v 1 < u 2 ∧ v 1 < w 0) ∧ ¬ (v 1 < u 0 ∧ v 1 < w 2)

/-- The array conditions: rows, diagonals and antidiagonals unimodal, columns nondecreasing. -/
def Good {L : ℕ} (x : Fin L → Fin 3 → Fin 4) : Prop :=
  (∀ i, LineOK (x i)) ∧
    (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j)) ∧
    (∀ i j l : Fin L, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TriOK (x i) (x j) (x l))

/-- a(n): the number of such n X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 3 → Fin 4 // Good x}

/-- The conjectured g.f. x*(50 + 184*x + 149*x^2 + 378*x^3 - 327*x^4 + 412*x^5 - 228*x^6 + 107*x^7 - 22*x^8 + 3*x^9) / (1 - x)^10. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (50 + 184 * PowerSeries.X + 149 * PowerSeries.X ^ 2 + 378 * PowerSeries.X ^ 3 - 327 * PowerSeries.X ^ 4 + 412 * PowerSeries.X ^ 5 - 228 * PowerSeries.X ^ 6 + 107 * PowerSeries.X ^ 7 - 22 * PowerSeries.X ^ 8 + 3 * PowerSeries.X ^ 9)) * ((1 - PowerSeries.X) ^ 10)⁻¹

/-- The recurrence (n > 10), the g.f. and the empirical closed form. -/
theorem main :
    (∀ n : ℕ, 11 ≤ n → (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 45 * (a (n - 2) : ℤ) + 120 * (a (n - 3) : ℤ) - 210 * (a (n - 4) : ℤ) + 252 * (a (n - 5) : ℤ) - 210 * (a (n - 6) : ℤ) + 120 * (a (n - 7) : ℤ) - 45 * (a (n - 8) : ℤ) + 10 * (a (n - 9) : ℤ) - (a (n - 10) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (353 / 181440) * (n : ℚ) ^ 9 + (17 / 560) * (n : ℚ) ^ 8 + (9083 / 30240) * (n : ℚ) ^ 7 + (1039 / 720) * (n : ℚ) ^ 6 + (46769 / 8640) * (n : ℚ) ^ 5 + (3863 / 360) * (n : ℚ) ^ 4 + (411149 / 22680) * (n : ℚ) ^ 3 + (14863 / 1260) * (n : ℚ) ^ 2 + (6497 / 1260) * (n : ℚ) - 3) := by
  sorry

end OMA.S_oeis_a224168
