import Mathlib

/-!
# A250756: Number of (1+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing x(i,j)+x(i-1,j) in the j direction

Source: https://oeis.org/A250756
Credit: @ivillar

Status: open conjecture (conjectures of Colin Barker, Nov 17 2018; empirical formula of the entry, R. H. Hardin, Nov 27 2014). A proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 32, 72, 129, 203, 294, 402, ...).
An array is a map x : Fin 2 → Fin (n+1) → Fin 3 (row i, column j, entries in 0..2). The two conditions of the
title compare neighbouring rows and neighbouring columns:
* nondecreasing x(i,j)-x(i,j-1) in the i direction: x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) for all i ≥ 1, j ≥ 1;
* nondecreasing x(i,j)+x(i-1,j) in the j direction: x(i,j-1)+x(i-1,j-1) ≤ x(i,j)+x(i-1,j) for all i ≥ 1, j ≥ 1.
Each of them involves exactly the 2 X 2 block formed by rows i-1, i and columns j-1, j, with entries
p = x(i-1,j-1), q = x(i-1,j), r = x(i,j-1), s = x(i,j).

Formulas of the entry, all stated in `main`:
* a(n) = (17/2)*n^2 + (29/2)*n + 9.  [empirical formula of the entry; stated for n ≥ 1, over ℚ]
* G.f.: x*(32 - 24*x + 9*x^2) / (1 - x)^3.  [conjecture of Colin Barker, Nov 17 2018; of Sum_{n ≥ 1} a(n) x^n, as a formal power series over ℚ]
* a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>3.  [conjecture of Colin Barker, Nov 17 2018; stated for n ≥ 4, over ℤ]
-/

namespace OMA.S_oeis_a250756

/-- The condition on a 2 X 2 block with upper row p, q (row i-1, columns j-1, j) and lower row r, s (row i):
x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) and x(i,j-1)+x(i-1,j-1) ≤ x(i,j)+x(i-1,j). -/
def Blk (p q r s : ℕ) : Prop :=
  (q : ℤ) - p ≤ (s : ℤ) - r ∧ r + p ≤ s + q

/-- a(n): the number of 2 X (n+1) arrays with entries in 0..2 all of whose 2 X 2 blocks satisfy `Blk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 2 → Fin (n + 1) → Fin 3 //
    ∀ i : Fin 1, ∀ j : Fin n,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)}

/-- The conjectured generating function x*(32 - 24*x + 9*x^2) / (1 - x)^3. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (32 - 24 * PowerSeries.X + 9 * PowerSeries.X ^ 2)) *
    ((1 - PowerSeries.X) ^ 3)⁻¹

/-- The conjectured formulas of the entry. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 17 / 2 * (n : ℚ) ^ 2 + 29 / 2 * (n : ℚ) + 9) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a250756
