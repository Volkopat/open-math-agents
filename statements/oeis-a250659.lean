import Mathlib

/-!
# A250659: Number of (5+1) X (n+1) 0..1 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction

Source: https://oeis.org/A250659
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Nov 26 2014; g.f. and recurrence conjectured by Colin Barker, Nov 15 2018); a proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 159, 286, 445, 636, 859, 1114, ...). An array is a map
x : Fin 6 → Fin (n + 1) → Fin 2 (row i, column j, value in 0..1).
The two conditions concern every 2 X 2 subblock, with rows i, i+1, columns j, j+1 and entries
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1):
* x(i,j)-x(i,j-1) is nondecreasing in the i direction: q - p ≤ s - r;
* min(x(i,j),x(i-1,j)) is nondecreasing in the j direction: min(p,r) ≤ min(q,s).

Conjectures of the entry:
* Empirical (Hardin): a(n) = 16*n^2 + 79*n + 64 (n ≥ 1, over ℚ);
* G.f. (Barker): x*(159 - 191*x + 64*x^2) / (1 - x)^3 (of Sum_{n ≥ 1} a(n) x^n, as a power series
  over ℚ);
* (Barker) a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>3 (over ℤ).
-/

namespace OMA.S_oeis_a250659

/-- The condition on a 2 X 2 subblock with upper row (p, q) and lower row (r, s), i.e.
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1). -/
def CellOK (p q r s : ℤ) : Prop := q - p ≤ s - r ∧ min p r ≤ min q s

/-- a(n): the number of 6 X (n+1) arrays with entries in 0..1 all of whose 2 X 2 subblocks satisfy
the condition. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 6 → Fin (n + 1) → Fin 2 // ∀ i : Fin 5, ∀ j : Fin n,
    CellOK ((x i.castSucc j.castSucc : ℕ) : ℤ) ((x i.castSucc j.succ : ℕ) : ℤ) ((x i.succ j.castSucc : ℕ) : ℤ) ((x i.succ j.succ : ℕ) : ℤ)}

/-- The conjectured g.f. x*(159 - 191*x + 64*x^2) / ((1 - x)^3). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (159 - 191 * PowerSeries.X + 64 * PowerSeries.X ^ 2)) * ((1 - PowerSeries.X) ^ 3)⁻¹

/-- The recurrence, the g.f. and the empirical formula. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 16 * (n : ℚ) ^ 2 + 79 * (n : ℚ) + 64) := by
  sorry

end OMA.S_oeis_a250659
