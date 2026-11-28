import Mathlib

/-!
# A250779: Number of (n+1) X (4+1) 0..1 arrays with nondecreasing x(i,j)+x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction

Source: https://oeis.org/A250779
Credit: @ivillar

Status: open conjecture (empirical recurrence of R. H. Hardin, Nov 27 2014; g.f. and closed form conjectured by Colin Barker, Nov 19 2018); a proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 99, 238, 534, 1152, 2426, 5028, ...). An array is a map
x : Fin (n + 1) → Fin 5 → Fin 2 (row i, column j, value in 0..1).
The two conditions concern every 2 X 2 subblock, with rows i, i+1, columns j, j+1 and entries
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1):
* x(i,j)+x(i,j-1) is nondecreasing in the i direction: p + q ≤ r + s;
* the absolute value of x(i,j)-x(i-1,j) is nondecreasing in the j direction: |r - p| ≤ |s - q|.

Conjectures of the entry:
* Empirical (Hardin): a(n) = 6*a(n-1) - 14*a(n-2) + 16*a(n-3) - 9*a(n-4) + 2*a(n-5) (stated for
  n ≥ 6, so that all indices are at least the offset 1; over ℤ);
* G.f. (Barker): x*(99 - 356*x + 492*x^2 - 304*x^3 + 73*x^4) / ((1 - x)^4*(1 - 2*x))
  (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
* a(n) = (-288 + 507*2^n - 116*n - 12*n^2 - 4*n^3) / 6 (Barker; n ≥ 1, over ℚ).
-/

namespace OMA.S_oeis_a250779

/-- The condition on a 2 X 2 subblock with upper row (p, q) and lower row (r, s), i.e.
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1). -/
def CellOK (p q r s : ℤ) : Prop := p + q ≤ r + s ∧ (r - p).natAbs ≤ (s - q).natAbs

/-- a(n): the number of (n+1) X 5 arrays with entries in 0..1 all of whose 2 X 2 subblocks satisfy
the condition. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 5 → Fin 2 // ∀ i : Fin n, ∀ j : Fin 4,
    CellOK ((x i.castSucc j.castSucc : ℕ) : ℤ) ((x i.castSucc j.succ : ℕ) : ℤ) ((x i.succ j.castSucc : ℕ) : ℤ) ((x i.succ j.succ : ℕ) : ℤ)}

/-- The conjectured g.f. x*(99 - 356*x + 492*x^2 - 304*x^3 + 73*x^4) / ((1 - x)^4*(1 - 2*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (99 - 356 * PowerSeries.X + 492 * PowerSeries.X ^ 2 - 304 * PowerSeries.X ^ 3 + 73 * PowerSeries.X ^ 4)) * ((1 - PowerSeries.X) ^ 4 * (1 - 2 * PowerSeries.X))⁻¹

/-- The empirical recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 14 * a (n - 2) + 16 * a (n - 3) - 9 * a (n - 4) + 2 * a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-288 + 507 * 2 ^ n - 116 * (n : ℚ) - 12 * (n : ℚ) ^ 2 - 4 * (n : ℚ) ^ 3) / 6) := by
  sorry

end OMA.S_oeis_a250779
