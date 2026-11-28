import Mathlib

/-!
# A224392: Number of 3 X n 0..3 arrays with diagonals and antidiagonals unimodal and rows nondecreasing

Source: https://oeis.org/A224392
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Apr 05 2013; g.f. and recurrence conjectured by
Colin Barker, Aug 30 2018).

R. H. Hardin's sequence (offset 1, data 64, 1000, 6094, 27790, 102232, 319769, ...). An array x(i,j) with rows i = 0..2 and
columns j = 0..n-1 is given by its columns: x : Fin n → Fin 3 → Fin 4, where x j i is the entry in row i and
column j (value in 0..3). Rows are nondecreasing: x(i,j) ≤ x(i,j+1).
An antidiagonal consists of the cells (i,j) with i+j constant; it has at most three cells, namely
x(2,j), x(1,j+1), x(0,j+2), and a sequence of at most two elements is always unimodal, so the antidiagonals
are unimodal exactly when no middle element is smaller than both of its neighbors on the antidiagonal.
The same holds for the diagonals, with cells x(0,j), x(1,j+1), x(2,j+2).

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (353/181440)*n^9 + (17/560)*n^8 + (9731/30240)*n^7 + (1283/720)*n^6 + (52457/8640)*n^5 + (776/45)*n^4 + (294499/11340)*n^3 + (28837/2520)*n^2 + (8207/126)*n - 18 for n > 1 (over ℚ);
G.f.: x*(64 + 360*x - 1026*x^2 + 4170*x^3 - 7998*x^4 + 10591*x^5 - 9351*x^6 + 5629*x^7 - 2165*x^8 + 478*x^9 - 46*x^10) / (1 - x)^10 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n > 11.
-/

namespace OMA.S_oeis_a224392

/-- Consecutive columns u (column j), v (column j+1): rows are nondecreasing. -/
def BlockOK (u v : Fin 3 → Fin 4) : Prop :=
  ∀ i : Fin 3, u i ≤ v i

/-- Three consecutive columns u, v, w (columns j, j+1, j+2): the antidiagonal x(2,j), x(1,j+1), x(0,j+2)
and the diagonal x(0,j), x(1,j+1), x(2,j+2) are unimodal. -/
def TriOK (u v w : Fin 3 → Fin 4) : Prop :=
  ¬ (v 1 < u 2 ∧ v 1 < w 0) ∧ ¬ (v 1 < u 0 ∧ v 1 < w 2)

/-- The array conditions: rows nondecreasing, diagonals and antidiagonals unimodal. -/
def Good {L : ℕ} (x : Fin L → Fin 3 → Fin 4) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j)) ∧
    (∀ i j l : Fin L, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TriOK (x i) (x j) (x l))

/-- a(n): the number of such 3 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 3 → Fin 4 // Good x}

/-- The conjectured g.f. x*(64 + 360*x - 1026*x^2 + 4170*x^3 - 7998*x^4 + 10591*x^5 - 9351*x^6 + 5629*x^7 - 2165*x^8 + 478*x^9 - 46*x^10) / (1 - x)^10. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (64 + 360 * PowerSeries.X - 1026 * PowerSeries.X ^ 2 + 4170 * PowerSeries.X ^ 3 - 7998 * PowerSeries.X ^ 4 + 10591 * PowerSeries.X ^ 5 - 9351 * PowerSeries.X ^ 6 + 5629 * PowerSeries.X ^ 7 - 2165 * PowerSeries.X ^ 8 + 478 * PowerSeries.X ^ 9 - 46 * PowerSeries.X ^ 10)) * ((1 - PowerSeries.X) ^ 10)⁻¹

/-- The recurrence (n > 11), the g.f. and the empirical closed form (n > 1). -/
theorem main :
    (∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 45 * (a (n - 2) : ℤ) + 120 * (a (n - 3) : ℤ) - 210 * (a (n - 4) : ℤ) + 252 * (a (n - 5) : ℤ) - 210 * (a (n - 6) : ℤ) + 120 * (a (n - 7) : ℤ) - 45 * (a (n - 8) : ℤ) + 10 * (a (n - 9) : ℤ) - (a (n - 10) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (353 / 181440) * (n : ℚ) ^ 9 + (17 / 560) * (n : ℚ) ^ 8 + (9731 / 30240) * (n : ℚ) ^ 7 + (1283 / 720) * (n : ℚ) ^ 6 + (52457 / 8640) * (n : ℚ) ^ 5 + (776 / 45) * (n : ℚ) ^ 4 + (294499 / 11340) * (n : ℚ) ^ 3 + (28837 / 2520) * (n : ℚ) ^ 2 + (8207 / 126) * (n : ℚ) - 18) := by
  sorry

end OMA.S_oeis_a224392
