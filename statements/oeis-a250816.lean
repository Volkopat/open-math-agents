import Mathlib

/-!
# A250816: Number of (4+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction

Source: https://oeis.org/A250816
Credit: @ivillar

Status: open conjecture (conjectures of Colin Barker, Nov 21 2018; empirical formula of the entry, R. H. Hardin, Nov 27 2014).

R. H. Hardin's sequence (offset 1, data 1389, 4321, 10233, 20631, 37333, 62469, ...).
An array is a map x : Fin 5 → Fin (n+1) → Fin 3 (row i, column j, entries in 0..2). The two conditions of the
title compare neighbouring rows and neighbouring columns:
* nondecreasing x(i,j)-x(i,j-1) in the i direction: x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) for all i ≥ 1, j ≥ 1;
* nondecreasing min(x(i,j),x(i-1,j)) in the j direction: min(x(i,j-1),x(i-1,j-1)) ≤ min(x(i,j),x(i-1,j)) for all i ≥ 1, j ≥ 1.
Each of them involves exactly the 2 X 2 block formed by rows i-1, i and columns j-1, j, with entries
p = x(i-1,j-1), q = x(i-1,j), r = x(i,j-1), s = x(i,j).

Formulas of the entry, all stated in `main`:
* a(n) = 13*n^4 + 121*n^3 + 439*n^2 + 573*n + 243.  [empirical formula of the entry; stated for n ≥ 1, over ℚ]
* G.f.: x*(1389 - 2624*x + 2518*x^2 - 1214*x^3 + 243*x^4) / (1 - x)^5.  [conjecture of Colin Barker, Nov 21 2018; of Sum_{n ≥ 1} a(n) x^n, as a formal power series over ℚ]
* a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.  [conjecture of Colin Barker, Nov 21 2018; stated for n ≥ 6, over ℤ]
-/

namespace OMA.S_oeis_a250816

/-- The condition on a 2 X 2 block with upper row p, q (row i-1, columns j-1, j) and lower row r, s (row i):
x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) and min(x(i,j-1),x(i-1,j-1)) ≤ min(x(i,j),x(i-1,j)). -/
def Blk (p q r s : ℕ) : Prop :=
  (q : ℤ) - p ≤ (s : ℤ) - r ∧ min r p ≤ min s q

/-- a(n): the number of 5 X (n+1) arrays with entries in 0..2 all of whose 2 X 2 blocks satisfy `Blk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 5 → Fin (n + 1) → Fin 3 //
    ∀ i : Fin 4, ∀ j : Fin n,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)}

/-- The conjectured generating function x*(1389 - 2624*x + 2518*x^2 - 1214*x^3 + 243*x^4) / (1 - x)^5. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (1389 - 2624 * PowerSeries.X + 2518 * PowerSeries.X ^ 2 - 1214 * PowerSeries.X ^ 3 + 243 * PowerSeries.X ^ 4)) *
    ((1 - PowerSeries.X) ^ 5)⁻¹

/-- The conjectured formulas of the entry. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 13 * (n : ℚ) ^ 4 + 121 * (n : ℚ) ^ 3 + 439 * (n : ℚ) ^ 2 + 573 * (n : ℚ) + 243) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a250816
