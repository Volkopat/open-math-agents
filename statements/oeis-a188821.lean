import Mathlib

/-!
# A188821: Number of n X 6 binary arrays without the pattern 0 1 diagonally or antidiagonally

Source: https://oeis.org/A188821
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Apr 11 2011; g.f. and recurrence conjectured by
Colin Barker, Apr 30 2018).

R. H. Hardin's sequence (offset 1, data 64, 441, 1296, 2704, 4624, 7056, ...). An array is a map
x : Fin n → Fin 6 → Fin 2 (row i, column j). The pattern 0 1 occurs diagonally when x(i,j) = 0 and
x(i+1,j+1) = 1, and antidiagonally when x(i,j) = 0 and x(i+1,j-1) = 1 (reading downwards, as in the
examples of the entry); neither may occur.

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = 256*n^2 - 384*n + 144 for n > 2;
G.f.: x*(64 + 249*x + 165*x^2 + 75*x^3 - 41*x^4) / (1 - x)^3 (of Sum_{n ≥ 1} a(n) x^n, over ℚ);
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n > 5.
-/

namespace OMA.S_oeis_a188821

/-- Consecutive rows u (row i), v (row i+1): no 0 in u with a 1 diagonally or antidiagonally below it. -/
def BlockOK (u v : Fin 6 → Fin 2) : Prop :=
  ∀ j j' : Fin 6, ((j' : ℕ) = j + 1 ∨ (j : ℕ) = j' + 1) → ¬ (u j = 0 ∧ v j' = 1)

/-- The array conditions: every two consecutive rows satisfy `BlockOK`. -/
def Good {L : ℕ} (x : Fin L → Fin 6 → Fin 2) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j))

/-- a(n): the number of such n X 6 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 6 → Fin 2 // Good x}

/-- The conjectured g.f. x*(64 + 249*x + 165*x^2 + 75*x^3 - 41*x^4) / (1 - x)^3. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (64 + 249 * PowerSeries.X + 165 * PowerSeries.X ^ 2 + 75 * PowerSeries.X ^ 3 - 41 * PowerSeries.X ^ 4)) * ((1 - PowerSeries.X) ^ 3)⁻¹

/-- The recurrence (n > 5), the g.f. and the empirical closed form (n > 2). -/
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 256 * (n : ℤ) ^ 2 - 384 * (n : ℤ) + 144) := by
  sorry

end OMA.S_oeis_a188821
