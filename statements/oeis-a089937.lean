import Mathlib

/-!
# A089937: Number of 6 X n matrices with entries {0,1} without adjacent 0's in any row or column. 6th row of A089934

Source: https://oeis.org/A089937
Credit: @ivillar

Status: known result (the g.f. was conjectured by Colin Barker, Jun 06 2017; Andrew Howroyd, Dec 24 2019, notes
in the entry that the conjecture is correct because the order of the recurrence is A089935(6) = 11).

Sequence of the entry (offset 1, data 21, 239, 2999, 36787, 454385, 5598861, ...); also the number of
independent vertex sets in the grid graph P_6 X P_n. A matrix with rows i = 0..5 and columns j = 0..n-1
is given by its columns: x : Fin n → Fin 6 → Fin 2, where x j i is the entry in row i and column j. No two
vertically adjacent entries (in a column) and no two horizontally adjacent entries (in a row) are both 0.

Formula of the entry formalized in `main`:
G.f.: x*(21 + 71*x - 215*x^2 - 385*x^3 + 668*x^4 + 234*x^5 - 400*x^6 + 9*x^7 + 49*x^8 - 3*x^9 - x^10) /
(1 - 8*x - 62*x^2 + 78*x^3 + 375*x^4 - 300*x^5 - 486*x^6 + 385*x^7 + 30*x^8 - 52*x^9 + 2*x^10 + x^11)
(of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ).
-/

namespace OMA.S_oeis_a089937

/-- A column has no two adjacent 0s. -/
def LineOK (u : Fin 6 → Fin 2) : Prop :=
  ∀ i i' : Fin 6, (i' : ℕ) = i + 1 → ¬ (u i = 0 ∧ u i' = 0)

/-- Consecutive columns u, v: no two horizontally adjacent 0s. -/
def BlockOK (u v : Fin 6 → Fin 2) : Prop :=
  ∀ i : Fin 6, ¬ (u i = 0 ∧ v i = 0)

/-- The matrix conditions: no two adjacent 0s in any column or row. -/
def Good {L : ℕ} (x : Fin L → Fin 6 → Fin 2) : Prop :=
  (∀ i, LineOK (x i)) ∧
    (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j))

/-- a(n): the number of such 6 X n matrices. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 6 → Fin 2 // Good x}

/-- The conjectured g.f. of the entry. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (21 + 71 * PowerSeries.X - 215 * PowerSeries.X ^ 2 - 385 * PowerSeries.X ^ 3 + 668 * PowerSeries.X ^ 4 + 234 * PowerSeries.X ^ 5 - 400 * PowerSeries.X ^ 6 + 9 * PowerSeries.X ^ 7 + 49 * PowerSeries.X ^ 8 - 3 * PowerSeries.X ^ 9 - PowerSeries.X ^ 10)) * (1 - 8 * PowerSeries.X - 62 * PowerSeries.X ^ 2 + 78 * PowerSeries.X ^ 3 + 375 * PowerSeries.X ^ 4 - 300 * PowerSeries.X ^ 5 - 486 * PowerSeries.X ^ 6 + 385 * PowerSeries.X ^ 7 + 30 * PowerSeries.X ^ 8 - 52 * PowerSeries.X ^ 9 + 2 * PowerSeries.X ^ 10 + PowerSeries.X ^ 11)⁻¹

/-- The g.f. of the entry. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  sorry

end OMA.S_oeis_a089937
