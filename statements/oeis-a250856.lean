import Mathlib

/-!
# A250856: Number of (4+1) X (n+1) 0..3 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction

Source: https://oeis.org/A250856
Credit: @ivillar

Status: open conjecture (conjectures of Colin Barker, Nov 21 2018; empirical formula of the entry, R. H. Hardin, Nov 28 2014).

R. H. Hardin's sequence (offset 1, data 12311, 63631, 223933, 626416, 1499679, 3204951, ...).
An array is a map x : Fin 5 → Fin (n+1) → Fin 4 (row i, column j, entries in 0..3). The two conditions of the
title compare neighbouring rows and neighbouring columns:
* nondecreasing x(i,j)-x(i,j-1) in the i direction: x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) for all i ≥ 1, j ≥ 1;
* nondecreasing min(x(i,j),x(i-1,j)) in the j direction: min(x(i,j-1),x(i-1,j-1)) ≤ min(x(i,j),x(i-1,j)) for all i ≥ 1, j ≥ 1.
Each of them involves exactly the 2 X 2 block formed by rows i-1, i and columns j-1, j, with entries
p = x(i-1,j-1), q = x(i-1,j), r = x(i,j-1), s = x(i,j).

Formulas of the entry, all stated in `main`:
* a(n) = (76/9)*n^6 + (1595/12)*n^5 + (28765/36)*n^4 + (31373/12)*n^3 + (155683/36)*n^2 + (10223/3)*n + 1024.  [empirical formula of the entry; stated for n ≥ 1, over ℚ]
* G.f.: x*(12311 - 22546*x + 37047*x^2 - 35749*x^3 + 21160*x^4 - 7167*x^5 + 1024*x^6) / (1 - x)^7.  [conjecture of Colin Barker, Nov 21 2018; of Sum_{n ≥ 1} a(n) x^n, as a formal power series over ℚ]
* a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.  [conjecture of Colin Barker, Nov 21 2018; stated for n ≥ 8, over ℤ]
-/

namespace OMA.S_oeis_a250856

/-- The condition on a 2 X 2 block with upper row p, q (row i-1, columns j-1, j) and lower row r, s (row i):
x(i-1,j)-x(i-1,j-1) ≤ x(i,j)-x(i,j-1) (as integers) and min(x(i,j-1),x(i-1,j-1)) ≤ min(x(i,j),x(i-1,j)). -/
def Blk (p q r s : ℕ) : Prop :=
  (q : ℤ) - p ≤ (s : ℤ) - r ∧ min r p ≤ min s q

/-- a(n): the number of 5 X (n+1) arrays with entries in 0..3 all of whose 2 X 2 blocks satisfy `Blk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 5 → Fin (n + 1) → Fin 4 //
    ∀ i : Fin 4, ∀ j : Fin n,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)}

/-- The conjectured generating function x*(12311 - 22546*x + 37047*x^2 - 35749*x^3 + 21160*x^4 - 7167*x^5 + 1024*x^6) / (1 - x)^7. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (12311 - 22546 * PowerSeries.X + 37047 * PowerSeries.X ^ 2 - 35749 * PowerSeries.X ^ 3 + 21160 * PowerSeries.X ^ 4 - 7167 * PowerSeries.X ^ 5 + 1024 * PowerSeries.X ^ 6)) *
    ((1 - PowerSeries.X) ^ 7)⁻¹

/-- The conjectured formulas of the entry. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 76 / 9 * (n : ℚ) ^ 6 + 1595 / 12 * (n : ℚ) ^ 5 + 28765 / 36 * (n : ℚ) ^ 4 + 31373 / 12 * (n : ℚ) ^ 3 + 155683 / 36 * (n : ℚ) ^ 2 + 10223 / 3 * (n : ℚ) + 1024) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a250856
