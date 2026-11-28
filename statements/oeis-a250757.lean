import Mathlib

/-!
# A250757: Number of (2+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing x(i,j)+x(i-1,j) in the j direction

Source: https://oeis.org/A250757
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Nov 27 2014; g.f. and recurrence conjectured by
Colin Barker, Nov 18 2018).

R. H. Hardin's sequence (offset 1, data 105, 237, 423, 663, 957, 1305, ...). An array x(i,j) with rows
i = 0..2 and columns j = 0..n is given by its columns: x : Fin (n+1) → Fin 3 → Fin 3, where x j i is the
entry in row i and column j (value in 0..2). The two conditions are, for consecutive columns j-1, j and
consecutive rows i-1, i: x(i-1,j) - x(i-1,j-1) ≤ x(i,j) - x(i,j-1) (the difference x(i,j)-x(i,j-1) is
nondecreasing in i), and x(i,j-1) + x(i-1,j-1) ≤ x(i,j) + x(i-1,j) (the sum is nondecreasing in j).

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = 27*n^2 + 51*n + 27 (n ≥ 1);
G.f.: 3*x*(35 - 26*x + 9*x^2) / (1 - x)^3 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n > 3.
-/

namespace OMA.S_oeis_a250757

/-- Consecutive columns u (column j-1), v (column j): both conditions for the rows i, i+1. -/
def BlockOK (u v : Fin 3 → Fin 3) : Prop :=
  ∀ i i' : Fin 3, (i' : ℕ) = i + 1 →
    ((v i : ℤ) - (u i : ℤ) ≤ (v i' : ℤ) - (u i' : ℤ)) ∧ (u i' : ℕ) + (u i : ℕ) ≤ (v i' : ℕ) + (v i : ℕ)

/-- The array conditions: every two consecutive columns satisfy `BlockOK`. -/
def Good {L : ℕ} (x : Fin L → Fin 3 → Fin 3) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j))

/-- a(n): the number of such 3 X (n+1) arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 3 → Fin 3 // Good x}

/-- The conjectured g.f. 3*x*(35 - 26*x + 9*x^2) / (1 - x)^3. -/
noncomputable def G : PowerSeries ℚ :=
  (3 * PowerSeries.X * (35 - 26 * PowerSeries.X + 9 * PowerSeries.X ^ 2)) * ((1 - PowerSeries.X) ^ 3)⁻¹

/-- The recurrence (n > 3), the g.f. and the empirical closed form. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 27 * (n : ℤ) ^ 2 + 51 * (n : ℤ) + 27) := by
  sorry

end OMA.S_oeis_a250757
