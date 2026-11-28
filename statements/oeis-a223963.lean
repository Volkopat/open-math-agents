import Mathlib

/-!
# A223963: Number of 3 X n 0..3 arrays with antidiagonals unimodal and rows and diagonals nondecreasing

Source: https://oeis.org/A223963
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Mar 29 2013; g.f. and recurrence conjectured by
Colin Barker, Aug 24 2018).

R. H. Hardin's sequence (offset 1, data 64, 707, 3471, 12311, 36028, 92734, ...). An array x(i,j) with rows i = 0..2 and
columns j = 0..n-1 is given by its columns: x : Fin n → Fin 3 → Fin 4, where x j i is the entry in row i and
column j (value in 0..3). Rows are nondecreasing: x(i,j) ≤ x(i,j+1).
Diagonals are nondecreasing: x(i,j) ≤ x(i+1,j+1).
An antidiagonal consists of the cells (i,j) with i+j constant; it has at most three cells, namely
x(2,j), x(1,j+1), x(0,j+2), and a sequence of at most two elements is always unimodal, so the antidiagonals
are unimodal exactly when no middle element is smaller than both of its neighbors on the antidiagonal.

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (1/8640)*n^9 + (1/320)*n^8 + (503/10080)*n^7 + (659/1440)*n^6 + (3013/960)*n^5 + (37141/2880)*n^4 + (106019/2160)*n^3 - (18977/720)*n^2 + (2711/70)*n - 6 for n > 2 (over ℚ);
G.f.: x*(64 + 67*x - 719*x^2 + 1736*x^3 - 2287*x^4 + 2271*x^5 - 2070*x^6 + 1632*x^7 - 910*x^8 + 311*x^9 - 58*x^10 + 5*x^11) / (1 - x)^10 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n > 12.
-/

namespace OMA.S_oeis_a223963

/-- Consecutive columns u (column j), v (column j+1): rows and diagonals are nondecreasing. -/
def BlockOK (u v : Fin 3 → Fin 4) : Prop :=
  (∀ i : Fin 3, u i ≤ v i) ∧ u 0 ≤ v 1 ∧ u 1 ≤ v 2

/-- Three consecutive columns u, v, w (columns j, j+1, j+2): the antidiagonal x(2,j), x(1,j+1), x(0,j+2)
is unimodal. -/
def TriOK (u v w : Fin 3 → Fin 4) : Prop :=
  ¬ (v 1 < u 2 ∧ v 1 < w 0)

/-- The array conditions: rows and diagonals nondecreasing, antidiagonals unimodal. -/
def Good {L : ℕ} (x : Fin L → Fin 3 → Fin 4) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j)) ∧
    (∀ i j l : Fin L, (j : ℕ) = i + 1 → (l : ℕ) = j + 1 → TriOK (x i) (x j) (x l))

/-- a(n): the number of such 3 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 3 → Fin 4 // Good x}

/-- The conjectured g.f. x*(64 + 67*x - 719*x^2 + 1736*x^3 - 2287*x^4 + 2271*x^5 - 2070*x^6 + 1632*x^7 - 910*x^8 + 311*x^9 - 58*x^10 + 5*x^11) / (1 - x)^10. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (64 + 67 * PowerSeries.X - 719 * PowerSeries.X ^ 2 + 1736 * PowerSeries.X ^ 3 - 2287 * PowerSeries.X ^ 4 + 2271 * PowerSeries.X ^ 5 - 2070 * PowerSeries.X ^ 6 + 1632 * PowerSeries.X ^ 7 - 910 * PowerSeries.X ^ 8 + 311 * PowerSeries.X ^ 9 - 58 * PowerSeries.X ^ 10 + 5 * PowerSeries.X ^ 11)) * ((1 - PowerSeries.X) ^ 10)⁻¹

/-- The recurrence (n > 12), the g.f. and the empirical closed form (n > 2). -/
theorem main :
    (∀ n : ℕ, 13 ≤ n → (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 45 * (a (n - 2) : ℤ) + 120 * (a (n - 3) : ℤ) - 210 * (a (n - 4) : ℤ) + 252 * (a (n - 5) : ℤ) - 210 * (a (n - 6) : ℤ) + 120 * (a (n - 7) : ℤ) - 45 * (a (n - 8) : ℤ) + 10 * (a (n - 9) : ℤ) - (a (n - 10) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = (1 / 8640) * (n : ℚ) ^ 9 + (1 / 320) * (n : ℚ) ^ 8 + (503 / 10080) * (n : ℚ) ^ 7 + (659 / 1440) * (n : ℚ) ^ 6 + (3013 / 960) * (n : ℚ) ^ 5 + (37141 / 2880) * (n : ℚ) ^ 4 + (106019 / 2160) * (n : ℚ) ^ 3 - (18977 / 720) * (n : ℚ) ^ 2 + (2711 / 70) * (n : ℚ) - 6) := by
  sorry

end OMA.S_oeis_a223963
