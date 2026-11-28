import Mathlib

/-!
# A250893: Number of (n+1) X (3+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction

Source: https://oeis.org/A250893
Credit: @ivillar

Status: open conjecture (empirical recurrence of R. H. Hardin, Nov 28 2014; g.f. and closed form conjectured by
Colin Barker, Nov 23 2018).

R. H. Hardin's sequence (offset 1, data 403, 1325, 4388, 14196, 44525, 136509, ...). An array is a map
x : Fin (n+1) → Fin 4 → Fin 3 (row i, column j, value in 0..2). The two conditions are, for consecutive
rows i-1, i and consecutive columns j-1, j: x(i-1,j) - x(i-1,j-1) ≤ x(i,j) - x(i,j-1) (the difference
x(i,j)-x(i,j-1) is nondecreasing in i), and |x(i,j-1) - x(i-1,j-1)| ≤ |x(i,j) - x(i-1,j)| (the absolute
value of x(i,j)-x(i-1,j) is nondecreasing in j).

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = 12*a(n-1) - 60*a(n-2) + 162*a(n-3) - 255*a(n-4) + 234*a(n-5) - 116*a(n-6) + 24*a(n-7) for n > 9;
G.f.: x*(403 - 3511*x + 12668*x^2 - 24246*x^3 + 25568*x^4 - 13314*x^5 + 1284*x^6 + 1746*x^7 - 594*x^8) /
((1 - x)^3*(1 - 2*x)^3*(1 - 3*x)) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (-8*(179+223*2^n-25*3^(3+n)) + (1104-845*2^n)*n + (32+375*2^n)*n^2) / 32 for n > 2 (over ℚ).
-/

namespace OMA.S_oeis_a250893

/-- Consecutive rows u (row i-1), v (row i): both conditions for the columns j, j+1. -/
def BlockOK (u v : Fin 4 → Fin 3) : Prop :=
  ∀ j j' : Fin 4, (j' : ℕ) = j + 1 →
    ((u j' : ℤ) - (u j : ℤ) ≤ (v j' : ℤ) - (v j : ℤ)) ∧ |(v j : ℤ) - (u j : ℤ)| ≤ |(v j' : ℤ) - (u j' : ℤ)|

/-- The array conditions: every two consecutive rows satisfy `BlockOK`. -/
def Good {L : ℕ} (x : Fin L → Fin 4 → Fin 3) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j))

/-- a(n): the number of such (n+1) X 4 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 4 → Fin 3 // Good x}

/-- The conjectured g.f. x*(403 - 3511*x + 12668*x^2 - 24246*x^3 + 25568*x^4 - 13314*x^5 + 1284*x^6 + 1746*x^7 - 594*x^8) /
((1 - x)^3*(1 - 2*x)^3*(1 - 3*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (403 - 3511 * PowerSeries.X + 12668 * PowerSeries.X ^ 2 - 24246 * PowerSeries.X ^ 3 + 25568 * PowerSeries.X ^ 4 - 13314 * PowerSeries.X ^ 5 + 1284 * PowerSeries.X ^ 6 + 1746 * PowerSeries.X ^ 7 - 594 * PowerSeries.X ^ 8)) * ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X) ^ 3 * (1 - 3 * PowerSeries.X))⁻¹

/-- The empirical recurrence (n > 9), the g.f. and the closed form (n > 2). -/
theorem main :
    (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 12 * (a (n - 1) : ℤ) - 60 * (a (n - 2) : ℤ) + 162 * (a (n - 3) : ℤ) - 255 * (a (n - 4) : ℤ) + 234 * (a (n - 5) : ℤ) - 116 * (a (n - 6) : ℤ) + 24 * (a (n - 7) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = (-8 * (179 + 223 * (2 : ℚ) ^ n - 25 * (3 : ℚ) ^ (3 + n)) + (1104 - 845 * (2 : ℚ) ^ n) * (n : ℚ) + (32 + 375 * (2 : ℚ) ^ n) * (n : ℚ) ^ 2) / 32) := by
  sorry

end OMA.S_oeis_a250893
