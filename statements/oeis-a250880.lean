import Mathlib

/-!
# A250880: Number of (3+1) X (n+1) 0..3 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing x(i,j)+x(i-1,j) in the j direction

Source: https://oeis.org/A250880
Credit: @ivillar

Status: open conjecture (conjectures of Colin Barker, Nov 22 2018; empirical formula of the entry, R. H. Hardin, Nov 28 2014).

R. H. Hardin's sequence (offset 1, data 2002, 6812, 16262, 31928, 55386, 88212, ...).
An array is a map x : Fin 4 → Fin (n+1) → Fin 4 (row i, column j, entries in 0..3). The two conditions of the
title compare neighbouring rows and neighbouring columns:
* nondecreasing x(i,j)-x(i,j-1) in the i direction: x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) for all i ≥ 1, j ≥ 1;
* nondecreasing x(i,j)+x(i-1,j) in the j direction: x(i,j-1)+x(i-1,j-1) ≤ x(i,j)+x(i-1,j) for all i ≥ 1, j ≥ 1.
Each of them involves exactly the 2 X 2 block formed by rows i-1, i and columns j-1, j, with entries
p = x(i-1,j-1), q = x(i-1,j), r = x(i,j-1), s = x(i,j).

Formulas of the entry, all stated in `main`:
* a(n) = (788/3)*n^3 + 744*n^2 + (2218/3)*n + 256.  [empirical formula of the entry; stated for n ≥ 1, over ℚ]
* G.f.: 2*x*(1001 - 598*x + 513*x^2 - 128*x^3) / (1 - x)^4.  [conjecture of Colin Barker, Nov 22 2018; of Sum_{n ≥ 1} a(n) x^n, as a formal power series over ℚ]
* a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.  [conjecture of Colin Barker, Nov 22 2018; stated for n ≥ 5, over ℤ]
-/

namespace OMA.S_oeis_a250880

/-- The condition on a 2 X 2 block with upper row p, q (row i-1, columns j-1, j) and lower row r, s (row i):
x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) and x(i,j-1)+x(i-1,j-1) ≤ x(i,j)+x(i-1,j). -/
def Blk (p q r s : ℕ) : Prop :=
  (q : ℤ) - p ≤ (s : ℤ) - r ∧ r + p ≤ s + q

/-- a(n): the number of 4 X (n+1) arrays with entries in 0..3 all of whose 2 X 2 blocks satisfy `Blk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 4 → Fin (n + 1) → Fin 4 //
    ∀ i : Fin 3, ∀ j : Fin n,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)}

/-- The conjectured generating function 2*x*(1001 - 598*x + 513*x^2 - 128*x^3) / (1 - x)^4. -/
noncomputable def G : PowerSeries ℚ :=
  (2 * PowerSeries.X * (1001 - 598 * PowerSeries.X + 513 * PowerSeries.X ^ 2 - 128 * PowerSeries.X ^ 3)) *
    ((1 - PowerSeries.X) ^ 4)⁻¹

/-- The conjectured formulas of the entry. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 788 / 3 * (n : ℚ) ^ 3 + 744 * (n : ℚ) ^ 2 + 2218 / 3 * (n : ℚ) + 256) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a250880
