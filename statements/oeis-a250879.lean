import Mathlib

/-!
# A250879: Number of (2+1) X (n+1) 0..3 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing x(i,j)+x(i-1,j) in the j direction

Source: https://oeis.org/A250879
Credit: @ivillar

Status: open conjecture (empirical formula of R. H. Hardin, Nov 28 2014; g.f. and recurrence conjectured by Colin Barker, Nov 22 2018); a proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 440, 1456, 3442, 6728, 11644, 18520, ...). An array is a map
x : Fin 3 → Fin (n + 1) → Fin 4 (row i, column j, value in 0..3).
The two conditions concern every 2 X 2 subblock, with rows i, i+1, columns j, j+1 and entries
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1):
* x(i,j)-x(i,j-1) is nondecreasing in the i direction: q - p ≤ s - r;
* x(i,j)+x(i-1,j) is nondecreasing in the j direction: p + r ≤ q + s.

Conjectures of the entry:
* Empirical (Hardin): a(n) = 55*n^3 + 155*n^2 + 166*n + 64 (n ≥ 1, over ℚ);
* G.f. (Barker): 2*x*(220 - 152*x + 129*x^2 - 32*x^3) / (1 - x)^4 (of Sum_{n ≥ 1} a(n) x^n, as a
  power series over ℚ);
* (Barker) a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4 (over ℤ).
-/

namespace OMA.S_oeis_a250879

/-- The condition on a 2 X 2 subblock with upper row (p, q) and lower row (r, s), i.e.
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1). -/
def CellOK (p q r s : ℤ) : Prop := q - p ≤ s - r ∧ p + r ≤ q + s

/-- a(n): the number of 3 X (n+1) arrays with entries in 0..3 all of whose 2 X 2 subblocks satisfy
the condition. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 3 → Fin (n + 1) → Fin 4 // ∀ i : Fin 2, ∀ j : Fin n,
    CellOK ((x i.castSucc j.castSucc : ℕ) : ℤ) ((x i.castSucc j.succ : ℕ) : ℤ) ((x i.succ j.castSucc : ℕ) : ℤ) ((x i.succ j.succ : ℕ) : ℤ)}

/-- The conjectured g.f. 2*x*(220 - 152*x + 129*x^2 - 32*x^3) / ((1 - x)^4). -/
noncomputable def G : PowerSeries ℚ :=
  (2 * PowerSeries.X * (220 - 152 * PowerSeries.X + 129 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 3)) * ((1 - PowerSeries.X) ^ 4)⁻¹

/-- The recurrence, the g.f. and the empirical formula. -/
theorem main :
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 55 * (n : ℚ) ^ 3 + 155 * (n : ℚ) ^ 2 + 166 * (n : ℚ) + 64) := by
  sorry

end OMA.S_oeis_a250879
