import Mathlib

/-!
# A250892: Number of (n+1) X (2+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction

Source: https://oeis.org/A250892
Credit: @ivillar

Status: open conjecture (conjectures of Colin Barker, Nov 22 2018; empirical formula of the entry, R. H. Hardin, Nov 28 2014). A proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 127, 431, 1450, 4750, 15111, 47061, ...).
An array is a map x : Fin (n+1) → Fin 3 → Fin 3 (row i, column j, entries in 0..2). The two conditions of the
title compare neighbouring rows and neighbouring columns:
* nondecreasing x(i,j)-x(i,j-1) in the i direction: x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) for all i ≥ 1, j ≥ 1;
* nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction: |x(i,j-1)-x(i-1,j-1)| ≤ |x(i,j)-x(i-1,j)| for all i ≥ 1, j ≥ 1.
Each of them involves exactly the 2 X 2 block formed by rows i-1, i and columns j-1, j, with entries
p = x(i-1,j-1), q = x(i-1,j), r = x(i,j-1), s = x(i,j).

Formulas of the entry, all stated in `main`:
* a(n) = 12*a(n-1) - 60*a(n-2) + 162*a(n-3) - 255*a(n-4) + 234*a(n-5) - 116*a(n-6) + 24*a(n-7) for n>9.  [empirical formula of the entry; stated for n ≥ 10, over ℤ]
* G.f.: x*(127 - 1093*x + 3898*x^2 - 7364*x^3 + 7674*x^4 - 3984*x^5 + 498*x^6 + 328*x^7 - 88*x^8) / ((1 - x)^3*(1 - 2*x)^3*(1 - 3*x)).  [conjecture of Colin Barker, Nov 22 2018; of Sum_{n ≥ 1} a(n) x^n, as a formal power series over ℚ]
* a(n) = (567 - 3807*2^n + 7225*3^n - 54*(-1+15*2^n)*n + 54*(-2+3*2^n)*n^2) / 108 for n>2.  [conjecture of Colin Barker, Nov 22 2018; stated for n ≥ 3, over ℚ]
-/

namespace OMA.S_oeis_a250892

/-- The condition on a 2 X 2 block with upper row p, q (row i-1, columns j-1, j) and lower row r, s (row i):
x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) and |x(i,j-1)-x(i-1,j-1)| ≤ |x(i,j)-x(i-1,j)|. -/
def Blk (p q r s : ℕ) : Prop :=
  (q : ℤ) - p ≤ (s : ℤ) - r ∧ |(r : ℤ) - p| ≤ |(s : ℤ) - q|

/-- a(n): the number of (n+1) X 3 arrays with entries in 0..2 all of whose 2 X 2 blocks satisfy `Blk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 3 → Fin 3 //
    ∀ i : Fin n, ∀ j : Fin 2,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)}

/-- The conjectured generating function x*(127 - 1093*x + 3898*x^2 - 7364*x^3 + 7674*x^4 - 3984*x^5 + 498*x^6 + 328*x^7 - 88*x^8) / ((1 - x)^3*(1 - 2*x)^3*(1 - 3*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (127 - 1093 * PowerSeries.X + 3898 * PowerSeries.X ^ 2 - 7364 * PowerSeries.X ^ 3 + 7674 * PowerSeries.X ^ 4 - 3984 * PowerSeries.X ^ 5 + 498 * PowerSeries.X ^ 6 + 328 * PowerSeries.X ^ 7 - 88 * PowerSeries.X ^ 8)) *
    ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X) ^ 3 * (1 - 3 * PowerSeries.X))⁻¹

/-- The conjectured formulas of the entry. -/
theorem main :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 12 * a (n - 1) - 60 * a (n - 2) + 162 * a (n - 3) - 255 * a (n - 4) + 234 * a (n - 5) - 116 * a (n - 6) + 24 * a (n - 7)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 2 < n → (a n : ℚ) = (567 - 3807 * 2 ^ n + 7225 * 3 ^ n - 54 * (-1 + 15 * 2 ^ n) * (n : ℚ) + 54 * (-2 + 3 * 2 ^ n) * (n : ℚ) ^ 2) / 108) := by
  sorry

end OMA.S_oeis_a250892
