import Mathlib

/-!
# A225009: Number of n X 7 0..1 arrays with rows unimodal and columns nondecreasing

Source: https://oeis.org/A225009
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Apr 23 2013; g.f. and recurrence conjectured by
Colin Barker, Sep 05 2018).

R. H. Hardin's sequence (offset 1, data 29, 239, 1163, 4166, 12174, 30738, ...). An array is a map
x : Fin n → Fin 7 → Fin 2 (row i, column j, value in 0..1). A row is unimodal when it is nondecreasing up
to some position k and nonincreasing from k on. Columns are nondecreasing: x(i,j) ≤ x(i+1,j).

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (4/315)*n^7 + (1/5)*n^6 + (58/45)*n^5 + (35/8)*n^4 + (1507/180)*n^3 + (357/40)*n^2 + (2027/420)*n + 1 (n ≥ 1, over ℚ);
G.f.: x*(29 + 7*x + 63*x^2 - 70*x^3 + 56*x^4 - 28*x^5 + 8*x^6 - x^7) / (1 - x)^8 (of Sum_{n ≥ 1} a(n) x^n, over ℚ);
a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n > 8.
-/

namespace OMA.S_oeis_a225009

/-- A row is unimodal: nondecreasing up to some position k, nonincreasing from k on. -/
def LineOK (u : Fin 7 → Fin 2) : Prop :=
  ∃ k : Fin 7, (∀ i j : Fin 7, i ≤ j → j ≤ k → u i ≤ u j) ∧ (∀ i j : Fin 7, k ≤ i → i ≤ j → u j ≤ u i)

/-- Consecutive rows u (row i), v (row i+1): columns are nondecreasing. -/
def BlockOK (u v : Fin 7 → Fin 2) : Prop :=
  ∀ j : Fin 7, u j ≤ v j

/-- The array conditions: every row is unimodal and every column is nondecreasing. -/
def Good {L : ℕ} (x : Fin L → Fin 7 → Fin 2) : Prop :=
  (∀ i, LineOK (x i)) ∧
    (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j))

/-- a(n): the number of such n X 7 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 7 → Fin 2 // Good x}

/-- The conjectured g.f. x*(29 + 7*x + 63*x^2 - 70*x^3 + 56*x^4 - 28*x^5 + 8*x^6 - x^7) / (1 - x)^8. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (29 + 7 * PowerSeries.X + 63 * PowerSeries.X ^ 2 - 70 * PowerSeries.X ^ 3 + 56 * PowerSeries.X ^ 4 - 28 * PowerSeries.X ^ 5 + 8 * PowerSeries.X ^ 6 - PowerSeries.X ^ 7)) * ((1 - PowerSeries.X) ^ 8)⁻¹

/-- The recurrence (n > 8), the g.f. and the empirical closed form. -/
theorem main :
    (∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (4 / 315) * (n : ℚ) ^ 7 + (1 / 5) * (n : ℚ) ^ 6 + (58 / 45) * (n : ℚ) ^ 5 + (35 / 8) * (n : ℚ) ^ 4 + (1507 / 180) * (n : ℚ) ^ 3 + (357 / 40) * (n : ℚ) ^ 2 + (2027 / 420) * (n : ℚ) + 1) := by
  sorry

end OMA.S_oeis_a225009
