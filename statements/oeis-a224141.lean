import Mathlib

/-!
# A224141: Number of n X 3 0..1 arrays with rows and antidiagonals unimodal and columns nondecreasing

Source: https://oeis.org/A224141
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Mar 31 2013; g.f. and recurrence conjectured by
Colin Barker, Aug 27 2018).

R. H. Hardin's sequence (offset 1, data 7, 22, 49, 92, 155, 242, ...). An array is a map
x : Fin n → Fin 3 → Fin 2 (row i, column j, value in 0..1). A row is unimodal when it is nondecreasing up
to some position k and nonincreasing from k on. Columns are nondecreasing: x(i,j) ≤ x(i+1,j).
An antidiagonal consists of the cells (i,j) with i+j constant; it has at most three cells, namely
x(i,2), x(i+1,1), x(i+2,0), and a sequence of at most two elements is always unimodal, so the antidiagonals
are unimodal exactly when no middle element is smaller than both of its neighbors on the antidiagonal.

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (2/3)*n^3 + 2*n^2 + (13/3)*n (n ≥ 1, over ℚ);
G.f.: x*(7 - 6*x + 3*x^2) / (1 - x)^4 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n > 4.
-/

namespace OMA.S_oeis_a224141

/-- A row is unimodal: nondecreasing up to some position k, nonincreasing from k on. -/
def LineOK (u : Fin 3 → Fin 2) : Prop :=
  ∃ k : Fin 3, (∀ i j : Fin 3, i ≤ j → j ≤ k → u i ≤ u j) ∧ (∀ i j : Fin 3, k ≤ i → i ≤ j → u j ≤ u i)

/-- Consecutive rows u (row i), v (row i+1): columns are nondecreasing. -/
def BlockOK (u v : Fin 3 → Fin 2) : Prop :=
  ∀ j : Fin 3, u j ≤ v j

/-- Three consecutive rows u, v, w (rows i, i+1, i+2): the antidiagonal x(i,2), x(i+1,1), x(i+2,0) is unimodal. -/
def TriOK (u v w : Fin 3 → Fin 2) : Prop :=
  ¬ (v 1 < u 2 ∧ v 1 < w 0)

/-- The array conditions: rows and antidiagonals unimodal, columns nondecreasing. -/
def Good {L : ℕ} (x : Fin L → Fin 3 → Fin 2) : Prop :=
  (∀ i, LineOK (x i)) ∧
    (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j)) ∧
    (∀ i j l : Fin L, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TriOK (x i) (x j) (x l))

/-- a(n): the number of such n X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 3 → Fin 2 // Good x}

/-- The conjectured g.f. x*(7 - 6*x + 3*x^2) / (1 - x)^4. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (7 - 6 * PowerSeries.X + 3 * PowerSeries.X ^ 2)) * ((1 - PowerSeries.X) ^ 4)⁻¹

/-- The recurrence (n > 4), the g.f. and the empirical closed form. -/
theorem main :
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 6 * (a (n - 2) : ℤ) + 4 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2 / 3) * (n : ℚ) ^ 3 + 2 * (n : ℚ) ^ 2 + (13 / 3) * (n : ℚ)) := by
  sorry

end OMA.S_oeis_a224141
