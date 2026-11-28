import Mathlib

/-!
# A250815: Number of (3+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction

Source: https://oeis.org/A250815
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Nov 27 2014; g.f. and recurrence conjectured by Colin Barker, Nov 21 2018); a proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 432, 1315, 3081, 6171, 11116, 18537, ...). An array is a map
x : Fin 4 → Fin (n + 1) → Fin 3 (row i, column j, value in 0..2).
The two conditions concern every 2 X 2 subblock, with rows i, i+1, columns j, j+1 and entries
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1):
* x(i,j)-x(i,j-1) is nondecreasing in the i direction: q - p ≤ s - r;
* min(x(i,j),x(i-1,j)) is nondecreasing in the j direction: min(p,r) ≤ min(q,s).

Conjectures of the entry:
* Empirical (Hardin): a(n) = (15/4)*n^4 + 36*n^3 + (527/4)*n^2 + (359/2)*n + 81 (n ≥ 1, over ℚ);
* G.f. (Barker): x*(432 - 845*x + 826*x^2 - 404*x^3 + 81*x^4) / (1 - x)^5 (of Sum_{n ≥ 1} a(n) x^n,
  as a power series over ℚ);
* (Barker) a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5 (over ℤ).
-/

namespace OMA.S_oeis_a250815

/-- The condition on a 2 X 2 subblock with upper row (p, q) and lower row (r, s), i.e.
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1). -/
def CellOK (p q r s : ℤ) : Prop := q - p ≤ s - r ∧ min p r ≤ min q s

/-- a(n): the number of 4 X (n+1) arrays with entries in 0..2 all of whose 2 X 2 subblocks satisfy
the condition. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 4 → Fin (n + 1) → Fin 3 // ∀ i : Fin 3, ∀ j : Fin n,
    CellOK ((x i.castSucc j.castSucc : ℕ) : ℤ) ((x i.castSucc j.succ : ℕ) : ℤ) ((x i.succ j.castSucc : ℕ) : ℤ) ((x i.succ j.succ : ℕ) : ℤ)}

/-- The conjectured g.f. x*(432 - 845*x + 826*x^2 - 404*x^3 + 81*x^4) / ((1 - x)^5). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (432 - 845 * PowerSeries.X + 826 * PowerSeries.X ^ 2 - 404 * PowerSeries.X ^ 3 + 81 * PowerSeries.X ^ 4)) * ((1 - PowerSeries.X) ^ 5)⁻¹

/-- The recurrence, the g.f. and the empirical formula. -/
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (15 / 4) * (n : ℚ) ^ 4 + 36 * (n : ℚ) ^ 3 + (527 / 4) * (n : ℚ) ^ 2 + (359 / 2) * (n : ℚ) + 81) := by
  sorry

end OMA.S_oeis_a250815
