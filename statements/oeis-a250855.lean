import Mathlib

/-!
# A250855: Number of (3+1) X (n+1) 0..3 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction

Source: https://oeis.org/A250855
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Nov 28 2014; g.f. and recurrence conjectured by Colin Barker, Nov 21 2018); a proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 2670, 13097, 44797, 123016, 290646, 614965, ...). An array is a map
x : Fin 4 → Fin (n + 1) → Fin 4 (row i, column j, value in 0..3).
The two conditions concern every 2 X 2 subblock, with rows i, i+1, columns j, j+1 and entries
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1):
* x(i,j)-x(i,j-1) is nondecreasing in the i direction: q - p ≤ s - r;
* min(x(i,j),x(i-1,j)) is nondecreasing in the j direction: min(p,r) ≤ min(q,s).

Conjectures of the entry:
* Empirical (Hardin): a(n) = (3/2)*n^6 + (74/3)*n^5 + (621/4)*n^4 + (3161/6)*n^3 + (3691/4)*n^2 +
  783*n + 256 (n ≥ 1, over ℚ);
* G.f. (Barker): x*(2670 - 5593*x + 9188*x^2 - 8976*x^3 + 5326*x^4 - 1791*x^5 + 256*x^6) / (1 - x)^7
  (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
* (Barker) a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for
  n>7 (over ℤ).
-/

namespace OMA.S_oeis_a250855

/-- The condition on a 2 X 2 subblock with upper row (p, q) and lower row (r, s), i.e.
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1). -/
def CellOK (p q r s : ℤ) : Prop := q - p ≤ s - r ∧ min p r ≤ min q s

/-- a(n): the number of 4 X (n+1) arrays with entries in 0..3 all of whose 2 X 2 subblocks satisfy
the condition. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 4 → Fin (n + 1) → Fin 4 // ∀ i : Fin 3, ∀ j : Fin n,
    CellOK ((x i.castSucc j.castSucc : ℕ) : ℤ) ((x i.castSucc j.succ : ℕ) : ℤ) ((x i.succ j.castSucc : ℕ) : ℤ) ((x i.succ j.succ : ℕ) : ℤ)}

/-- The conjectured g.f. x*(2670 - 5593*x + 9188*x^2 - 8976*x^3 + 5326*x^4 - 1791*x^5 + 256*x^6) / ((1 - x)^7). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (2670 - 5593 * PowerSeries.X + 9188 * PowerSeries.X ^ 2 - 8976 * PowerSeries.X ^ 3 + 5326 * PowerSeries.X ^ 4 - 1791 * PowerSeries.X ^ 5 + 256 * PowerSeries.X ^ 6)) * ((1 - PowerSeries.X) ^ 7)⁻¹

/-- The recurrence, the g.f. and the empirical formula. -/
theorem main :
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (3 / 2) * (n : ℚ) ^ 6 + (74 / 3) * (n : ℚ) ^ 5 + (621 / 4) * (n : ℚ) ^ 4 + (3161 / 6) * (n : ℚ) ^ 3 + (3691 / 4) * (n : ℚ) ^ 2 + 783 * (n : ℚ) + 256) := by
  sorry

end OMA.S_oeis_a250855
