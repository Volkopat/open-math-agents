import Mathlib

/-!
# A251132: Number of (n+1) X (3+1) 0..2 arrays with no 2 X 2 subblock having the sum of its diagonal elements greater than the maximum of its antidiagonal elements

Source: https://oeis.org/A251132
Credit: @ivillar

Status: open conjecture (conjectures of Colin Barker, Nov 26 2018; empirical formula of the entry, R. H. Hardin, Nov 30 2014). A proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 369, 1002, 1997, 4110, 8050, 15830, ...).
An array is a map x : Fin (n+1) → Fin 4 → Fin 3 (row i, column j, entries in 0..2); its 2 X 2 subblocks
are formed by rows i, i+1 and columns j, j+1, with entries p = x(i,j), q = x(i,j+1), r = x(i+1,j),
s = x(i+1,j+1). The condition on every subblock: the sum of the diagonal elements x(i,j) + x(i+1,j+1) is not greater than the maximum of the antidiagonal
elements x(i,j+1), x(i+1,j).

Formulas of the entry, all stated in `main`:
* a(n) = 6*a(n-1) - 13*a(n-2) + 10*a(n-3) + 5*a(n-4) - 14*a(n-5) + 9*a(n-6) - 2*a(n-7) for n>10.  [empirical formula of the entry; stated for n ≥ 11, over ℤ]
* G.f.: x*(369 - 1212*x + 782*x^2 + 1464*x^3 - 2514*x^4 + 1146*x^5 + 62*x^6 - 114*x^7 - 5*x^8 + 2*x^9) / ((1 - x)^5*(1 + x)*(1 - 2*x)).  [conjecture of Colin Barker, Nov 26 2018; of Sum_{n ≥ 1} a(n) x^n, as a formal power series over ℚ]
* a(n) = (36*(-5+9*(-1)^n+9*2^(3+n)) + 202*n + 151*n^2 + 50*n^3 + 5*n^4) / 12 for n>3.  [conjecture of Colin Barker, Nov 26 2018; stated for n ≥ 4, over ℚ]
-/

namespace OMA.S_oeis_a251132

/-- The condition on a 2 X 2 subblock with upper row p, q and lower row r, s: the sum p + s of its diagonal
elements is not greater than the maximum of its antidiagonal elements q, r. -/
def Blk (p q r s : ℕ) : Prop :=
  ¬ (max q r < p + s)

/-- a(n): the number of (n+1) X 4 arrays with entries in 0..2 all of whose 2 X 2 subblocks satisfy `Blk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 4 → Fin 3 //
    ∀ i : Fin n, ∀ j : Fin 3,
      Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)}

/-- The conjectured generating function x*(369 - 1212*x + 782*x^2 + 1464*x^3 - 2514*x^4 + 1146*x^5 + 62*x^6 - 114*x^7 - 5*x^8 + 2*x^9) / ((1 - x)^5*(1 + x)*(1 - 2*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (369 - 1212 * PowerSeries.X + 782 * PowerSeries.X ^ 2 + 1464 * PowerSeries.X ^ 3 - 2514 * PowerSeries.X ^ 4 + 1146 * PowerSeries.X ^ 5 + 62 * PowerSeries.X ^ 6 - 114 * PowerSeries.X ^ 7 - 5 * PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 9)) *
    ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) * (1 - 2 * PowerSeries.X))⁻¹

/-- The conjectured formulas of the entry. -/
theorem main :
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 6 * a (n - 1) - 13 * a (n - 2) + 10 * a (n - 3) + 5 * a (n - 4) - 14 * a (n - 5) + 9 * a (n - 6) - 2 * a (n - 7)) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 3 < n → (a n : ℚ) = (36 * (-5 + 9 * (-1) ^ n + 9 * 2 ^ (3 + n)) + 202 * (n : ℚ) + 151 * (n : ℚ) ^ 2 + 50 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 4) / 12) := by
  sorry

end OMA.S_oeis_a251132
