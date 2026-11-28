import Mathlib

/-!
# A250759: Number of (4+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing x(i,j)+x(i-1,j) in the j direction

Source: https://oeis.org/A250759
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Nov 27 2014; g.f. and recurrence conjectured by Colin Barker, Nov 18 2018); a proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 1029, 2361, 4239, 6663, 9633, 13149, ...). An array is a map
x : Fin 5 → Fin (n + 1) → Fin 3 (row i, column j, value in 0..2).
The two conditions concern every 2 X 2 subblock, with rows i, i+1, columns j, j+1 and entries
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1):
* x(i,j)-x(i,j-1) is nondecreasing in the i direction: q - p ≤ s - r;
* x(i,j)+x(i-1,j) is nondecreasing in the j direction: p + r ≤ q + s.

Conjectures of the entry:
* Empirical (Hardin): a(n) = 273*n^2 + 513*n + 243 (n ≥ 1, over ℚ);
* G.f. (Barker): 3*x*(343 - 242*x + 81*x^2) / (1 - x)^3 (of Sum_{n ≥ 1} a(n) x^n, as a power series
  over ℚ);
* (Barker) a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>3 (over ℤ).
-/

namespace OMA.S_oeis_a250759

/-- The condition on a 2 X 2 subblock with upper row (p, q) and lower row (r, s), i.e.
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1). -/
def CellOK (p q r s : ℤ) : Prop := q - p ≤ s - r ∧ p + r ≤ q + s

/-- a(n): the number of 5 X (n+1) arrays with entries in 0..2 all of whose 2 X 2 subblocks satisfy
the condition. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 5 → Fin (n + 1) → Fin 3 // ∀ i : Fin 4, ∀ j : Fin n,
    CellOK ((x i.castSucc j.castSucc : ℕ) : ℤ) ((x i.castSucc j.succ : ℕ) : ℤ) ((x i.succ j.castSucc : ℕ) : ℤ) ((x i.succ j.succ : ℕ) : ℤ)}

/-- The conjectured g.f. 3*x*(343 - 242*x + 81*x^2) / ((1 - x)^3). -/
noncomputable def G : PowerSeries ℚ :=
  (3 * PowerSeries.X * (343 - 242 * PowerSeries.X + 81 * PowerSeries.X ^ 2)) * ((1 - PowerSeries.X) ^ 3)⁻¹

/-- The recurrence, the g.f. and the empirical formula. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 273 * (n : ℚ) ^ 2 + 513 * (n : ℚ) + 243) := by
  sorry

end OMA.S_oeis_a250759
