import Mathlib

/-!
# A224185: Number of n X 3 0..2 arrays with rows unimodal and columns nondecreasing

Source: https://oeis.org/A224185
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Apr 01 2013; g.f. and recurrence conjectured by
Colin Barker, Aug 29 2018).

R. H. Hardin's sequence (offset 1, data 22, 158, 684, 2205, 5852, 13524, ...). An array is a map
x : Fin n → Fin 3 → Fin 3 (row i, column j, value in 0..2). A row is unimodal when it is nondecreasing up
to some position k and nonincreasing from k on. Columns are nondecreasing: x(i,j) ≤ x(i+1,j).

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (23/360)*n^6 + (27/40)*n^5 + (205/72)*n^4 + (49/8)*n^3 + (319/45)*n^2 + (21/5)*n + 1 (n ≥ 1, over ℚ);
G.f.: x*(22 + 4*x + 40*x^2 - 35*x^3 + 21*x^4 - 7*x^5 + x^6) / (1 - x)^7 (of Sum_{n ≥ 1} a(n) x^n, over ℚ);
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n > 7.
-/

namespace OMA.S_oeis_a224185

/-- A row is unimodal: nondecreasing up to some position k, nonincreasing from k on. -/
def LineOK (u : Fin 3 → Fin 3) : Prop :=
  ∃ k : Fin 3, (∀ i j : Fin 3, i ≤ j → j ≤ k → u i ≤ u j) ∧ (∀ i j : Fin 3, k ≤ i → i ≤ j → u j ≤ u i)

/-- Consecutive rows u (row i), v (row i+1): columns are nondecreasing. -/
def BlockOK (u v : Fin 3 → Fin 3) : Prop :=
  ∀ j : Fin 3, u j ≤ v j

/-- The array conditions: every row is unimodal and every column is nondecreasing. -/
def Good {L : ℕ} (x : Fin L → Fin 3 → Fin 3) : Prop :=
  (∀ i, LineOK (x i)) ∧
    (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j))

/-- a(n): the number of such n X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 3 → Fin 3 // Good x}

/-- The conjectured g.f. x*(22 + 4*x + 40*x^2 - 35*x^3 + 21*x^4 - 7*x^5 + x^6) / (1 - x)^7. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (22 + 4 * PowerSeries.X + 40 * PowerSeries.X ^ 2 - 35 * PowerSeries.X ^ 3 + 21 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6)) * ((1 - PowerSeries.X) ^ 7)⁻¹

/-- The recurrence (n > 7), the g.f. and the empirical closed form. -/
theorem main :
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 7 * (a (n - 1) : ℤ) - 21 * (a (n - 2) : ℤ) + 35 * (a (n - 3) : ℤ) - 35 * (a (n - 4) : ℤ) + 21 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) + (a (n - 7) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (23 / 360) * (n : ℚ) ^ 6 + (27 / 40) * (n : ℚ) ^ 5 + (205 / 72) * (n : ℚ) ^ 4 + (49 / 8) * (n : ℚ) ^ 3 + (319 / 45) * (n : ℚ) ^ 2 + (21 / 5) * (n : ℚ) + 1) := by
  sorry

end OMA.S_oeis_a224185
