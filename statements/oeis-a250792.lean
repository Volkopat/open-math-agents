import Mathlib

/-!
# A250792: Number of (n+1) X (3+1) 0..1 arrays with nondecreasing min(x(i,j),x(i,j-1)) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction

Source: https://oeis.org/A250792
Credit: @ivillar

Status: open conjecture (conjectures of Colin Barker, Nov 20 2018; empirical formula of the entry, R. H. Hardin, Nov 27 2014). A proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 54, 162, 482, 1430, 4258, 12706, ...).
An array is a map x : Fin (n+1) → Fin 4 → Fin 2 (row i, column j, entries in 0..1). The two conditions of the
title compare neighbouring rows and neighbouring columns:
* nondecreasing min(x(i,j),x(i,j-1)) in the i direction: min(x(i-1,j),x(i-1,j-1)) ≤ min(x(i,j),x(i,j-1)) for all i ≥ 1, j ≥ 1;
* nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction: |x(i,j-1)-x(i-1,j-1)| ≤ |x(i,j)-x(i-1,j)| for all i ≥ 1, j ≥ 1.
Each of them involves exactly the 2 X 2 block formed by rows i-1, i and columns j-1, j, with entries
p = x(i-1,j-1), q = x(i-1,j), r = x(i,j-1), s = x(i,j).

Formulas of the entry, all stated in `main`:
* a(n) = 6*a(n-1) - 10*a(n-2) + 11*a(n-4) - 6*a(n-5).  [empirical formula of the entry; stated for n ≥ 6, so that all indices are at least the offset 1, over ℤ]
* G.f.: 2*x*(27 - 81*x + 25*x^2 + 79*x^3 - 48*x^4) / ((1 - x)^2*(1 + x)*(1 - 2*x)*(1 - 3*x)).  [conjecture of Colin Barker, Nov 20 2018; of Sum_{n ≥ 1} a(n) x^n, as a formal power series over ℚ]
* a(n) = -3 - (-1)^n/4 + 2^(1+n) + (23*3^(1+n))/4 + n.  [conjecture of Colin Barker, Nov 20 2018; stated for n ≥ 1, over ℚ]
-/

namespace OMA.S_oeis_a250792

/-- The condition on a 2 X 2 block with upper row p, q (row i-1, columns j-1, j) and lower row r, s (row i):
min(x(i-1,j),x(i-1,j-1)) ≤ min(x(i,j),x(i,j-1)) and |x(i,j-1)-x(i-1,j-1)| ≤ |x(i,j)-x(i-1,j)|. -/
def Blk (p q r s : ℕ) : Prop :=
  min q p ≤ min s r ∧ |(r : ℤ) - p| ≤ |(s : ℤ) - q|

/-- a(n): the number of (n+1) X 4 arrays with entries in 0..1 all of whose 2 X 2 blocks satisfy `Blk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 4 → Fin 2 //
    ∀ i : Fin n, ∀ j : Fin 3,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)}

/-- The conjectured generating function 2*x*(27 - 81*x + 25*x^2 + 79*x^3 - 48*x^4) / ((1 - x)^2*(1 + x)*(1 - 2*x)*(1 - 3*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (2 * PowerSeries.X * (27 - 81 * PowerSeries.X + 25 * PowerSeries.X ^ 2 + 79 * PowerSeries.X ^ 3 - 48 * PowerSeries.X ^ 4)) *
    ((1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X))⁻¹

/-- The conjectured formulas of the entry. -/
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 10 * a (n - 2) + 11 * a (n - 4) - 6 * a (n - 5)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = -3 - (-1) ^ n / 4 + 2 ^ (1 + n) + 23 * 3 ^ (1 + n) / 4 + (n : ℚ)) := by
  sorry

end OMA.S_oeis_a250792
