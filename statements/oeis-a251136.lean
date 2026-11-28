import Mathlib

/-!
# A251136: Number of (n+1) X (7+1) 0..2 arrays with no 2 X 2 subblock having the sum of its diagonal elements greater than the maximum of its antidiagonal elements

Source: https://oeis.org/A251136
Credit: @ivillar

Status: open conjecture (conjectures of Colin Barker, Nov 26 2018; empirical formula of the entry, R. H. Hardin, Nov 30 2014).

R. H. Hardin's sequence (offset 1, data 10033, 19548, 30770, 51679, 82431, 135959, ...).
An array is a map x : Fin (n+1) → Fin 8 → Fin 3 (row i, column j, entries in 0..2); its 2 X 2 subblocks
are formed by rows i, i+1 and columns j, j+1, with entries p = x(i,j), q = x(i,j+1), r = x(i+1,j),
s = x(i+1,j+1). The condition on every subblock: the sum of the diagonal elements x(i,j) + x(i+1,j+1) is not greater than the maximum of the antidiagonal
elements x(i,j+1), x(i+1,j).

Formulas of the entry, all stated in `main`:
* a(n) = 6*a(n-1) - 13*a(n-2) + 10*a(n-3) + 5*a(n-4) - 14*a(n-5) + 9*a(n-6) - 2*a(n-7) for n>10.  [empirical formula of the entry; stated for n ≥ 11, over ℤ]
* G.f.: x*(10033 - 40650*x + 43911*x^2 + 20853*x^3 - 73278*x^4 + 48222*x^5 - 7753*x^6 - 1661*x^7 + 61*x^8 + 2*x^9) / ((1 - x)^5*(1 + x)*(1 - 2*x)).  [conjecture of Colin Barker, Nov 26 2018; of Sum_{n ≥ 1} a(n) x^n, as a formal power series over ℚ]
* a(n) = (68472 + 6724*(-1)^n + 1369*2^(3+n) + 34882*n + 8827*n^2 + 1130*n^3 + 65*n^4) / 12 for n>3.  [conjecture of Colin Barker, Nov 26 2018; stated for n ≥ 4, over ℚ]
-/

namespace OMA.S_oeis_a251136

/-- The condition on a 2 X 2 subblock with upper row p, q and lower row r, s: the sum p + s of its diagonal
elements is not greater than the maximum of its antidiagonal elements q, r. -/
def Blk (p q r s : ℕ) : Prop :=
  ¬ (max q r < p + s)

/-- a(n): the number of (n+1) X 8 arrays with entries in 0..2 all of whose 2 X 2 subblocks satisfy `Blk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 8 → Fin 3 //
    ∀ i : Fin n, ∀ j : Fin 7,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)}

/-- The conjectured generating function x*(10033 - 40650*x + 43911*x^2 + 20853*x^3 - 73278*x^4 + 48222*x^5 - 7753*x^6 - 1661*x^7 + 61*x^8 + 2*x^9) / ((1 - x)^5*(1 + x)*(1 - 2*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (10033 - 40650 * PowerSeries.X + 43911 * PowerSeries.X ^ 2 + 20853 * PowerSeries.X ^ 3 - 73278 * PowerSeries.X ^ 4 + 48222 * PowerSeries.X ^ 5 - 7753 * PowerSeries.X ^ 6 - 1661 * PowerSeries.X ^ 7 + 61 * PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 9)) *
    ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) * (1 - 2 * PowerSeries.X))⁻¹

/-- The conjectured formulas of the entry. -/
theorem main :
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 6 * a (n - 1) - 13 * a (n - 2) + 10 * a (n - 3) + 5 * a (n - 4) - 14 * a (n - 5) + 9 * a (n - 6) - 2 * a (n - 7)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 3 < n → (a n : ℚ) = (68472 + 6724 * (-1) ^ n + 1369 * 2 ^ (3 + n) + 34882 * (n : ℚ) + 8827 * (n : ℚ) ^ 2 + 1130 * (n : ℚ) ^ 3 + 65 * (n : ℚ) ^ 4) / 12) := by
  sorry

end OMA.S_oeis_a251136
