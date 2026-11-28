import Mathlib

/-!
# A251133: Number of (n+1) X (4+1) 0..2 arrays with no 2 X 2 subblock having the sum of its diagonal elements greater than the maximum of its antidiagonal elements

Source: https://oeis.org/A251133
Credit: @ivillar

Status: open conjecture (empirical recurrence of R. H. Hardin, Nov 30 2014; g.f. and closed form conjectured by
Colin Barker, Nov 26 2018).

R. H. Hardin's sequence (offset 1, data 919, 2264, 4110, 8008, 14753, 27738, ...). An array is a map
x : Fin (n+1) → Fin 5 → Fin 3 (row i, column j, value in 0..2). In the 2 X 2 subblock with rows i, i+1 and
columns j, j+1 the diagonal elements are x(i,j), x(i+1,j+1) and the antidiagonal elements are x(i,j+1),
x(i+1,j); the condition is x(i,j) + x(i+1,j+1) ≤ max(x(i,j+1), x(i+1,j)) for every subblock.

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = 6*a(n-1) - 13*a(n-2) + 10*a(n-3) + 5*a(n-4) - 14*a(n-5) + 9*a(n-6) - 2*a(n-7) for n > 10;
G.f.: x*(919 - 3250*x + 2473*x^2 + 3590*x^3 - 7100*x^4 + 3770*x^5 - 165*x^6 - 290*x^7 + 7*x^8 + 2*x^9) /
((1 - x)^5*(1 + x)*(1 - 2*x)) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (3063 + 961*(-1)^n + 121*2^(5+n) + 1726*n + 691*n^2 + 146*n^3 + 11*n^4) / 12 for n > 3 (over ℚ).
-/

namespace OMA.S_oeis_a251133

/-- Consecutive rows u (row i), v (row i+1): the condition for the subblocks in columns j, j+1. -/
def BlockOK (u v : Fin 5 → Fin 3) : Prop :=
  ∀ j j' : Fin 5, (j' : ℕ) = j + 1 → (u j : ℕ) + (v j' : ℕ) ≤ max (u j' : ℕ) (v j : ℕ)

/-- The array conditions: every two consecutive rows satisfy `BlockOK`. -/
def Good {L : ℕ} (x : Fin L → Fin 5 → Fin 3) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j))

/-- a(n): the number of such (n+1) X 5 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 5 → Fin 3 // Good x}

/-- The conjectured g.f. x*(919 - 3250*x + 2473*x^2 + 3590*x^3 - 7100*x^4 + 3770*x^5 - 165*x^6 - 290*x^7 + 7*x^8 + 2*x^9) /
((1 - x)^5*(1 + x)*(1 - 2*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (919 - 3250 * PowerSeries.X + 2473 * PowerSeries.X ^ 2 + 3590 * PowerSeries.X ^ 3 - 7100 * PowerSeries.X ^ 4 + 3770 * PowerSeries.X ^ 5 - 165 * PowerSeries.X ^ 6 - 290 * PowerSeries.X ^ 7 + 7 * PowerSeries.X ^ 8 + 2 * PowerSeries.X ^ 9)) * ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) * (1 - 2 * PowerSeries.X))⁻¹

/-- The empirical recurrence (n > 10), the g.f. and the closed form (n > 3). -/
theorem main :
    (∀ n : ℕ, 11 ≤ n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 13 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) + 5 * (a (n - 4) : ℤ) - 14 * (a (n - 5) : ℤ) + 9 * (a (n - 6) : ℤ) - 2 * (a (n - 7) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℚ) = (3063 + 961 * (-1 : ℚ) ^ n + 121 * (2 : ℚ) ^ (5 + n) + 1726 * (n : ℚ) + 691 * (n : ℚ) ^ 2 + 146 * (n : ℚ) ^ 3 + 11 * (n : ℚ) ^ 4) / 12) := by
  sorry

end OMA.S_oeis_a251133
