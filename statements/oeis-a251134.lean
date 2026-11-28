import Mathlib

/-!
# A251134: Number of (n+1) X (5+1) 0..2 arrays with no 2 X 2 subblock having the sum of its diagonal elements greater than the maximum of its antidiagonal elements

Source: https://oeis.org/A251134
Credit: @ivillar

Status: open conjecture (R. H. Hardin's empirical recurrence, Nov 30 2014; g.f. and closed form
conjectured by Colin Barker, Nov 26 2018).

R. H. Hardin's sequence (offset 1, data 2129, 4786, 8050, 14753, 25597, 46023, ...). An array is a
map x : Fin (n+1) → Fin 6 → Fin 3 (row i, column j, entries 0..2). Its 2 X 2 subblocks are formed by
rows i, i+1 and columns j, j+1; the diagonal elements of a subblock are x(i,j), x(i+1,j+1) and the
antidiagonal elements are x(i,j+1), x(i+1,j) (see PairOK). a(n) is the number of such arrays.

Conjectures of the entry, all three stated in `main`:
a(n) = 6*a(n-1) - 13*a(n-2) + 10*a(n-3) + 5*a(n-4) - 14*a(n-5) + 9*a(n-6) - 2*a(n-7) for n>10
(stated for n ≥ 11, so that all indices are at least the offset 1; over ℤ);
G.f.: x*(2129 - 7988*x + 7011*x^2 + 7381*x^3 - 16776*x^4 + 9606*x^5 - 883*x^6 - 571*x^7 + 21*x^8 +
2*x^9) / ((1 - x)^5*(1 + x)*(1 - 2*x)) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (2*(5472+1058*(-1)^n+2809*2^n) + 6142*n + 1759*n^2 + 266*n^3 + 17*n^4) / 12 for n>3 (n ≥ 4,
over ℚ).
-/

namespace OMA.S_oeis_a251134

/-- The condition on the 2 X 2 subblocks formed by two consecutive rows u = x(i,·), v = x(i+1,·) and two
consecutive columns j, j+1 (here j.castSucc and j.succ): the sum x(i,j) + x(i+1,j+1) of the diagonal elements is
not greater than the maximum of the antidiagonal elements x(i,j+1), x(i+1,j). -/
def PairOK (u v : Fin 6 → Fin 3) : Prop :=
  ∀ j : Fin 5,
    ¬ ((u j.castSucc : ℕ) + (v j.succ : ℕ) > max (u j.succ : ℕ) (v j.castSucc : ℕ))

/-- a(n): the number of such (n+1) X 6 arrays x (row i, column j, entries 0..2). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 6 → Fin 3 // ∀ i : Fin n, PairOK (x i.castSucc) (x i.succ)}

/-- The conjectured g.f. x*(2129 - 7988*x + 7011*x^2 + 7381*x^3 - 16776*x^4 + 9606*x^5 - 883*x^6 - 571*x^7 + 21*x^8 + 2*x^9) / ((1 - x)^5*(1 + x)*(1 - 2*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (2129 * PowerSeries.X - 7988 * PowerSeries.X ^ 2 + 7011 * PowerSeries.X ^ 3 + 7381 * PowerSeries.X ^ 4 - 16776 * PowerSeries.X ^ 5 + 9606 * PowerSeries.X ^ 6 - 883 * PowerSeries.X ^ 7 - 571 * PowerSeries.X ^ 8 + 21 * PowerSeries.X ^ 9 + 2 * PowerSeries.X ^ 10) * ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) * (1 - 2 * PowerSeries.X))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 11 ≤ n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 13 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) + 5 * (a (n - 4) : ℤ) - 14 * (a (n - 5) : ℤ) + 9 * (a (n - 6) : ℤ) - 2 * (a (n - 7) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℚ) = (2 * (5472 + 1058 * (-1 : ℚ) ^ n + 2809 * (2 : ℚ) ^ n) + 6142 * (n : ℚ) + 1759 * (n : ℚ) ^ 2 + 266 * (n : ℚ) ^ 3 + 17 * (n : ℚ) ^ 4) / 12) := by
  sorry

end OMA.S_oeis_a251134
