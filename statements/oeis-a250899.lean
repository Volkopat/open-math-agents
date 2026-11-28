import Mathlib

/-!
# A250899: Number of (1+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction

Source: https://oeis.org/A250899
Credit: @ivillar

Status: open conjecture (empirical recurrence of R. H. Hardin, Nov 28 2014; g.f. and closed form conjectured by Colin Barker, Nov 23 2018); a proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 37, 127, 403, 1229, 3673, 10875, ...). An array is a map
x : Fin 2 → Fin (n + 1) → Fin 3 (row i, column j, value in 0..2).
The two conditions concern every 2 X 2 subblock, with rows i, i+1, columns j, j+1 and entries
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1):
* x(i,j)-x(i,j-1) is nondecreasing in the i direction: q - p ≤ s - r;
* the absolute value of x(i,j)-x(i-1,j) is nondecreasing in the j direction: |r - p| ≤ |s - q|.

Conjectures of the entry:
* Empirical (Hardin): a(n) = 9*a(n-1) - 31*a(n-2) + 51*a(n-3) - 40*a(n-4) + 12*a(n-5) (stated for
  n ≥ 6, so that all indices are at least the offset 1; over ℤ);
* G.f. (Barker): x*(37 - 206*x + 407*x^2 - 348*x^3 + 108*x^4) / ((1 - x)^2*(1 - 2*x)^2*(1 - 3*x))
  (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
* a(n) = (7 - 2^(4+n) + 3^(3+n) + (2+2^(3+n))*n) / 2 (Barker; n ≥ 1, over ℚ).
-/

namespace OMA.S_oeis_a250899

/-- The condition on a 2 X 2 subblock with upper row (p, q) and lower row (r, s), i.e.
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1). -/
def CellOK (p q r s : ℤ) : Prop := q - p ≤ s - r ∧ (r - p).natAbs ≤ (s - q).natAbs

/-- a(n): the number of 2 X (n+1) arrays with entries in 0..2 all of whose 2 X 2 subblocks satisfy
the condition. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 2 → Fin (n + 1) → Fin 3 // ∀ i : Fin 1, ∀ j : Fin n,
    CellOK ((x i.castSucc j.castSucc : ℕ) : ℤ) ((x i.castSucc j.succ : ℕ) : ℤ) ((x i.succ j.castSucc : ℕ) : ℤ) ((x i.succ j.succ : ℕ) : ℤ)}

/-- The conjectured g.f. x*(37 - 206*x + 407*x^2 - 348*x^3 + 108*x^4) / ((1 - x)^2*(1 - 2*x)^2*(1 - 3*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (37 - 206 * PowerSeries.X + 407 * PowerSeries.X ^ 2 - 348 * PowerSeries.X ^ 3 + 108 * PowerSeries.X ^ 4)) * ((1 - PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X) ^ 2 * (1 - 3 * PowerSeries.X))⁻¹

/-- The empirical recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 9 * a (n - 1) - 31 * a (n - 2) + 51 * a (n - 3) - 40 * a (n - 4) + 12 * a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (7 - 2 ^ (4 + n) + 3 ^ (3 + n) + (2 + 2 ^ (3 + n)) * n) / 2) := by
  sorry

end OMA.S_oeis_a250899
