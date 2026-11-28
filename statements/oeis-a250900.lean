import Mathlib

/-!
# A250900: Number of (2+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction

Source: https://oeis.org/A250900
Credit: @ivillar

Status: open conjecture (conjectures of Colin Barker, Nov 23 2018; empirical formula of the entry, R. H. Hardin, Nov 28 2014). A proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 125, 431, 1325, 3867, 11029, 31215, ...).
An array is a map x : Fin 3 → Fin (n+1) → Fin 3 (row i, column j, entries in 0..2). The two conditions of the
title compare neighbouring rows and neighbouring columns:
* nondecreasing x(i,j)-x(i,j-1) in the i direction: x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) for all i ≥ 1, j ≥ 1;
* nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction: |x(i,j-1)-x(i-1,j-1)| ≤ |x(i,j)-x(i-1,j)| for all i ≥ 1, j ≥ 1.
Each of them involves exactly the 2 X 2 block formed by rows i-1, i and columns j-1, j, with entries
p = x(i-1,j-1), q = x(i-1,j), r = x(i,j-1), s = x(i,j).

Formulas of the entry, all stated in `main`:
* a(n) = 10*a(n-1) - 40*a(n-2) + 82*a(n-3) - 91*a(n-4) + 52*a(n-5) - 12*a(n-6).  [empirical formula of the entry; stated for n ≥ 7, so that all indices are at least the offset 1, over ℤ]
* G.f.: x*(125 - 819*x + 2015*x^2 - 2393*x^3 + 1392*x^4 - 324*x^5) / ((1 - x)^3*(1 - 2*x)^2*(1 - 3*x)).  [conjecture of Colin Barker, Nov 23 2018; of Sum_{n ≥ 1} a(n) x^n, as a formal power series over ℚ]
* a(n) = 23/2 - 2^(4+n) + (7*3^(2+n))/2 + 2*n + 3*2^(3+n)*n + n^2.  [conjecture of Colin Barker, Nov 23 2018; stated for n ≥ 1, over ℚ]
-/

namespace OMA.S_oeis_a250900

/-- The condition on a 2 X 2 block with upper row p, q (row i-1, columns j-1, j) and lower row r, s (row i):
x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) and |x(i,j-1)-x(i-1,j-1)| ≤ |x(i,j)-x(i-1,j)|. -/
def Blk (p q r s : ℕ) : Prop :=
  (q : ℤ) - p ≤ (s : ℤ) - r ∧ |(r : ℤ) - p| ≤ |(s : ℤ) - q|

/-- a(n): the number of 3 X (n+1) arrays with entries in 0..2 all of whose 2 X 2 blocks satisfy `Blk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 3 → Fin (n + 1) → Fin 3 //
    ∀ i : Fin 2, ∀ j : Fin n,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)}

/-- The conjectured generating function x*(125 - 819*x + 2015*x^2 - 2393*x^3 + 1392*x^4 - 324*x^5) / ((1 - x)^3*(1 - 2*x)^2*(1 - 3*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (125 - 819 * PowerSeries.X + 2015 * PowerSeries.X ^ 2 - 2393 * PowerSeries.X ^ 3 + 1392 * PowerSeries.X ^ 4 - 324 * PowerSeries.X ^ 5)) *
    ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X) ^ 2 * (1 - 3 * PowerSeries.X))⁻¹

/-- The conjectured formulas of the entry. -/
theorem main :
    (∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 10 * a (n - 1) - 40 * a (n - 2) + 82 * a (n - 3) - 91 * a (n - 4) + 52 * a (n - 5) - 12 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 23 / 2 - 2 ^ (4 + n) + 7 * 3 ^ (2 + n) / 2 + 2 * (n : ℚ) + 3 * 2 ^ (3 + n) * (n : ℚ) + (n : ℚ) ^ 2) := by
  sorry

end OMA.S_oeis_a250900
