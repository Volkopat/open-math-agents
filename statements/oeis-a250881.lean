import Mathlib

/-!
# A250881: Number of (4+1) X (n+1) 0..3 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing x(i,j)+x(i-1,j) in the j direction

Source: https://oeis.org/A250881
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Nov 28 2014; g.f. and recurrence conjectured by
Colin Barker, Nov 22 2018).

R. H. Hardin's sequence (offset 1, data 8736, 30360, 73122, 144248, 250964, 400496, ...). An array x(i,j) with rows
i = 0..4 and columns j = 0..n is given by its columns: x : Fin (n+1) → Fin 5 → Fin 4, where x j i is the
entry in row i and column j (value in 0..3). The two conditions are, for consecutive columns j-1, j and
consecutive rows i-1, i: x(i-1,j) - x(i-1,j-1) ≤ x(i,j) - x(i,j-1) (the difference x(i,j)-x(i,j-1) is
nondecreasing in i), and x(i,j-1) + x(i-1,j-1) ≤ x(i,j) + x(i-1,j) (the sum is nondecreasing in j).

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = (3613/3)*n^3 + 3343*n^2 + (9494/3)*n + 1024 (n ≥ 1, over ℚ);
G.f.: 2*x*(4368 - 2292*x + 2049*x^2 - 512*x^3) / (1 - x)^4 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n > 4.
-/

namespace OMA.S_oeis_a250881

/-- Consecutive columns u (column j-1), v (column j): both conditions for the rows i, i+1. -/
def BlockOK (u v : Fin 5 → Fin 4) : Prop :=
  ∀ i i' : Fin 5, (i' : ℕ) = i + 1 →
    ((v i : ℤ) - (u i : ℤ) ≤ (v i' : ℤ) - (u i' : ℤ)) ∧ (u i' : ℕ) + (u i : ℕ) ≤ (v i' : ℕ) + (v i : ℕ)

/-- The array conditions: every two consecutive columns satisfy `BlockOK`. -/
def Good {L : ℕ} (x : Fin L → Fin 5 → Fin 4) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j))

/-- a(n): the number of such 5 X (n+1) arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 5 → Fin 4 // Good x}

/-- The conjectured g.f. 2*x*(4368 - 2292*x + 2049*x^2 - 512*x^3) / (1 - x)^4. -/
noncomputable def G : PowerSeries ℚ :=
  (2 * PowerSeries.X * (4368 - 2292 * PowerSeries.X + 2049 * PowerSeries.X ^ 2 - 512 * PowerSeries.X ^ 3)) * ((1 - PowerSeries.X) ^ 4)⁻¹

/-- The recurrence (n > 4), the g.f. and the empirical closed form. -/
theorem main :
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 6 * (a (n - 2) : ℤ) + 4 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (3613 / 3) * (n : ℚ) ^ 3 + 3343 * (n : ℚ) ^ 2 + (9494 / 3) * (n : ℚ) + 1024) := by
  sorry

end OMA.S_oeis_a250881
