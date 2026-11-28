import Mathlib

/-!
# A250661: Number of (7+1) X (n+1) 0..1 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction

Source: https://oeis.org/A250661
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Nov 26 2014; g.f. and recurrence conjectured by
Colin Barker, Nov 16 2018).

R. H. Hardin's sequence (offset 1, data 639, 1150, 1789, 2556, 3451, 4474, ...). An array x(i,j) with rows
i = 0..7 and columns j = 0..n is given by its columns: x : Fin (n+1) → Fin 8 → Fin 2, where x j i is the
entry in row i and column j (value in 0..1). The two conditions are, for consecutive columns j-1, j and
consecutive rows i-1, i: x(i-1,j) - x(i-1,j-1) ≤ x(i,j) - x(i,j-1) (the difference x(i,j)-x(i,j-1) is
nondecreasing in i), and min(x(i,j-1), x(i-1,j-1)) ≤ min(x(i,j), x(i-1,j)) (the minimum is nondecreasing in j).

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = 64*n^2 + 319*n + 256 (n ≥ 1);
G.f.: x*(639 - 767*x + 256*x^2) / (1 - x)^3 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n > 3.
-/

namespace OMA.S_oeis_a250661

/-- Consecutive columns u (column j-1), v (column j): both conditions for the rows i, i+1. -/
def BlockOK (u v : Fin 8 → Fin 2) : Prop :=
  ∀ i i' : Fin 8, (i' : ℕ) = i + 1 →
    ((v i : ℤ) - (u i : ℤ) ≤ (v i' : ℤ) - (u i' : ℤ)) ∧ min (u i') (u i) ≤ min (v i') (v i)

/-- The array conditions: every two consecutive columns satisfy `BlockOK`. -/
def Good {L : ℕ} (x : Fin L → Fin 8 → Fin 2) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j))

/-- a(n): the number of such 8 X (n+1) arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 8 → Fin 2 // Good x}

/-- The conjectured g.f. x*(639 - 767*x + 256*x^2) / (1 - x)^3. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (639 - 767 * PowerSeries.X + 256 * PowerSeries.X ^ 2)) * ((1 - PowerSeries.X) ^ 3)⁻¹

/-- The recurrence (n > 3), the g.f. and the empirical closed form. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 64 * (n : ℤ) ^ 2 + 319 * (n : ℤ) + 256) := by
  sorry

end OMA.S_oeis_a250661
