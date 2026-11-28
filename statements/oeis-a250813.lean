import Mathlib

/-!
# A250813: Number of (1+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction

Source: https://oeis.org/A250813
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Nov 27 2014; g.f. and recurrence conjectured by
Colin Barker, Nov 21 2018).

R. H. Hardin's sequence (offset 1, data 36, 100, 225, 441, 784, 1296, ...). An array x(i,j) with rows
i = 0, 1 and columns j = 0..n is given by its columns: x : Fin (n+1) → Fin 2 → Fin 3, where x j i is the
entry in row i and column j (value in 0..2). The two conditions are, for consecutive columns j-1, j and
consecutive rows i-1, i: x(i-1,j) - x(i-1,j-1) ≤ x(i,j) - x(i,j-1) (the difference x(i,j)-x(i,j-1) is
nondecreasing in i), and min(x(i,j-1), x(i-1,j-1)) ≤ min(x(i,j), x(i-1,j)) (the minimum is nondecreasing in j).

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (1/4)*n^4 + (5/2)*n^3 + (37/4)*n^2 + 15*n + 9 (n ≥ 1, over ℚ);
G.f.: x*(36 - 80*x + 85*x^2 - 44*x^3 + 9*x^4) / (1 - x)^5 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 5.
-/

namespace OMA.S_oeis_a250813

/-- Consecutive columns u (column j-1), v (column j): both conditions for the rows i, i+1. -/
def BlockOK (u v : Fin 2 → Fin 3) : Prop :=
  ∀ i i' : Fin 2, (i' : ℕ) = i + 1 →
    ((v i : ℤ) - (u i : ℤ) ≤ (v i' : ℤ) - (u i' : ℤ)) ∧ min (u i') (u i) ≤ min (v i') (v i)

/-- The array conditions: every two consecutive columns satisfy `BlockOK`. -/
def Good {L : ℕ} (x : Fin L → Fin 2 → Fin 3) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j))

/-- a(n): the number of such 2 X (n+1) arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 2 → Fin 3 // Good x}

/-- The conjectured g.f. x*(36 - 80*x + 85*x^2 - 44*x^3 + 9*x^4) / (1 - x)^5. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (36 - 80 * PowerSeries.X + 85 * PowerSeries.X ^ 2 - 44 * PowerSeries.X ^ 3 + 9 * PowerSeries.X ^ 4)) * ((1 - PowerSeries.X) ^ 5)⁻¹

/-- The recurrence (n > 5), the g.f. and the empirical closed form. -/
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 10 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1 / 4) * (n : ℚ) ^ 4 + (5 / 2) * (n : ℚ) ^ 3 + (37 / 4) * (n : ℚ) ^ 2 + 15 * (n : ℚ) + 9) := by
  sorry

end OMA.S_oeis_a250813
