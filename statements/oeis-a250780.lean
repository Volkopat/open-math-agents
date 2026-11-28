import Mathlib

/-!
# A250780: Number of (n+1) X (5+1) 0..1 arrays with nondecreasing x(i,j)+x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction

Source: https://oeis.org/A250780
Credit: @ivillar

Status: open conjecture (conjectures of Colin Barker, Nov 19 2018; empirical formula of the entry, R. H. Hardin, Nov 27 2014). A proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 209, 518, 1194, 2640, 5688, 12036, ...).
An array is a map x : Fin (n+1) → Fin 6 → Fin 2 (row i, column j, entries in 0..1). The two conditions of the
title compare neighbouring rows and neighbouring columns:
* nondecreasing x(i,j)+x(i,j-1) in the i direction: x(i-1,j)+x(i-1,j-1) ≤ x(i,j)+x(i,j-1) for all i ≥ 1, j ≥ 1;
* nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction: |x(i,j-1)-x(i-1,j-1)| ≤ |x(i,j)-x(i-1,j)| for all i ≥ 1, j ≥ 1.
Each of them involves exactly the 2 X 2 block formed by rows i-1, i and columns j-1, j, with entries
p = x(i-1,j-1), q = x(i-1,j), r = x(i,j-1), s = x(i,j).

Formulas of the entry, all stated in `main`:
* a(n) = 8*a(n-1) - 27*a(n-2) + 50*a(n-3) - 55*a(n-4) + 36*a(n-5) - 13*a(n-6) + 2*a(n-7).  [empirical formula of the entry; stated for n ≥ 8, so that all indices are at least the offset 1, over ℤ]
* G.f.: x*(209 - 1154*x + 2693*x^2 - 3376*x^3 + 2401*x^4 - 922*x^5 + 153*x^6) / ((1 - x)^6*(1 - 2*x)).  [conjecture of Colin Barker, Nov 19 2018; of Sum_{n ≥ 1} a(n) x^n, as a formal power series over ℚ]
* a(n) = (9/2)*(49*2^n-32) - (374*n)/5 - 9*n^2 - (25*n^3)/6 - n^5/30.  [conjecture of Colin Barker, Nov 19 2018; stated for n ≥ 1, over ℚ]
-/

namespace OMA.S_oeis_a250780

/-- The condition on a 2 X 2 block with upper row p, q (row i-1, columns j-1, j) and lower row r, s (row i):
x(i-1,j)+x(i-1,j-1) ≤ x(i,j)+x(i,j-1) and |x(i,j-1)-x(i-1,j-1)| ≤ |x(i,j)-x(i-1,j)|. -/
def Blk (p q r s : ℕ) : Prop :=
  p + q ≤ r + s ∧ |(r : ℤ) - p| ≤ |(s : ℤ) - q|

/-- a(n): the number of (n+1) X 6 arrays with entries in 0..1 all of whose 2 X 2 blocks satisfy `Blk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 6 → Fin 2 //
    ∀ i : Fin n, ∀ j : Fin 5,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)}

/-- The conjectured generating function x*(209 - 1154*x + 2693*x^2 - 3376*x^3 + 2401*x^4 - 922*x^5 + 153*x^6) / ((1 - x)^6*(1 - 2*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (209 - 1154 * PowerSeries.X + 2693 * PowerSeries.X ^ 2 - 3376 * PowerSeries.X ^ 3 + 2401 * PowerSeries.X ^ 4 - 922 * PowerSeries.X ^ 5 + 153 * PowerSeries.X ^ 6)) *
    ((1 - PowerSeries.X) ^ 6 * (1 - 2 * PowerSeries.X))⁻¹

/-- The conjectured formulas of the entry. -/
theorem main :
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 8 * a (n - 1) - 27 * a (n - 2) + 50 * a (n - 3) - 55 * a (n - 4) + 36 * a (n - 5) - 13 * a (n - 6) + 2 * a (n - 7)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 9 / 2 * (49 * 2 ^ n - 32) - 374 * (n : ℚ) / 5 - 9 * (n : ℚ) ^ 2 - 25 * (n : ℚ) ^ 3 / 6 - (n : ℚ) ^ 5 / 30) := by
  sorry

end OMA.S_oeis_a250780
