import Mathlib

/-!
# A250660: Number of (6+1) X (n+1) 0..1 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction

Source: https://oeis.org/A250660
Credit: @ivillar

Status: open conjecture (conjectures of Colin Barker, Nov 15 2018; empirical formula of the entry, R. H. Hardin, Nov 26 2014). A proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 319, 574, 893, 1276, 1723, 2234, ...).
An array is a map x : Fin 7 → Fin (n+1) → Fin 2 (row i, column j, entries in 0..1). The two conditions of the
title compare neighbouring rows and neighbouring columns:
* nondecreasing x(i,j)-x(i,j-1) in the i direction: x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) for all i ≥ 1, j ≥ 1;
* nondecreasing min(x(i,j),x(i-1,j)) in the j direction: min(x(i,j-1),x(i-1,j-1)) ≤ min(x(i,j),x(i-1,j)) for all i ≥ 1, j ≥ 1.
Each of them involves exactly the 2 X 2 block formed by rows i-1, i and columns j-1, j, with entries
p = x(i-1,j-1), q = x(i-1,j), r = x(i,j-1), s = x(i,j).

Formulas of the entry, all stated in `main`:
* a(n) = 32*n^2 + 159*n + 128.  [empirical formula of the entry; stated for n ≥ 1, over ℚ]
* G.f.: x*(319 - 383*x + 128*x^2) / (1 - x)^3.  [conjecture of Colin Barker, Nov 15 2018; of Sum_{n ≥ 1} a(n) x^n, as a formal power series over ℚ]
* a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>3.  [conjecture of Colin Barker, Nov 15 2018; stated for n ≥ 4, over ℤ]
-/

namespace OMA.S_oeis_a250660

/-- The condition on a 2 X 2 block with upper row p, q (row i-1, columns j-1, j) and lower row r, s (row i):
x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) and min(x(i,j-1),x(i-1,j-1)) ≤ min(x(i,j),x(i-1,j)). -/
def Blk (p q r s : ℕ) : Prop :=
  (q : ℤ) - p ≤ (s : ℤ) - r ∧ min r p ≤ min s q

/-- a(n): the number of 7 X (n+1) arrays with entries in 0..1 all of whose 2 X 2 blocks satisfy `Blk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 7 → Fin (n + 1) → Fin 2 //
    ∀ i : Fin 6, ∀ j : Fin n,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)}

/-- The conjectured generating function x*(319 - 383*x + 128*x^2) / (1 - x)^3. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (319 - 383 * PowerSeries.X + 128 * PowerSeries.X ^ 2)) *
    ((1 - PowerSeries.X) ^ 3)⁻¹

/-- The conjectured formulas of the entry. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 32 * (n : ℚ) ^ 2 + 159 * (n : ℚ) + 128) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a250660
