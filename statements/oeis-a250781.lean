import Mathlib

/-!
# A250781: Number of (n+1) X (6+1) 0..1 arrays with nondecreasing x(i,j)+x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction

Source: https://oeis.org/A250781
Credit: @ivillar

Status: open conjecture (empirical recurrence of R. H. Hardin, Nov 27 2014; g.f. and closed form conjectured by
Colin Barker, Nov 19 2018).

R. H. Hardin's sequence (offset 1, data 436, 1106, 2604, 5882, 12950, 27986, ...). An array is a map
x : Fin (n+1) → Fin 7 → Fin 2 (row i, column j, value in 0..1). The two conditions are, for consecutive
rows i-1, i and consecutive columns j-1, j: x(i-1,j) + x(i-1,j-1) ≤ x(i,j) + x(i,j-1) (the sum
x(i,j)+x(i,j-1) is nondecreasing in i), and |x(i,j-1) - x(i-1,j-1)| ≤ |x(i,j) - x(i-1,j)| (the absolute
value of x(i,j)-x(i-1,j) is nondecreasing in j).

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = 10*a(n-1) - 44*a(n-2) + 112*a(n-3) - 182*a(n-4) + 196*a(n-5) - 140*a(n-6) + 64*a(n-7) - 17*a(n-8) + 2*a(n-9)
(for n ≥ 10, all indices at least the offset 1);
G.f.: 2*x*(218 - 1627*x + 5364*x^2 - 10163*x^3 + 12093*x^4 - 9259*x^5 + 4469*x^6 - 1253*x^7 + 160*x^8) / ((1 - x)^8*(1 - 2*x))
(of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (2520*(289*2^n-209) - 314796*n - 41972*n^2 - 23779*n^3 + 385*n^4 - 364*n^5 + 7*n^6 - n^7) / 1260 (n ≥ 1, over ℚ).
-/

namespace OMA.S_oeis_a250781

/-- Consecutive rows u (row i-1), v (row i): both conditions for the columns j, j+1. -/
def BlockOK (u v : Fin 7 → Fin 2) : Prop :=
  ∀ j j' : Fin 7, (j' : ℕ) = j + 1 →
    ((u j' : ℕ) + (u j : ℕ) ≤ (v j' : ℕ) + (v j : ℕ)) ∧ |(v j : ℤ) - (u j : ℤ)| ≤ |(v j' : ℤ) - (u j' : ℤ)|

/-- The array conditions: every two consecutive rows satisfy `BlockOK`. -/
def Good {L : ℕ} (x : Fin L → Fin 7 → Fin 2) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j))

/-- a(n): the number of such (n+1) X 7 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 7 → Fin 2 // Good x}

/-- The conjectured g.f. 2*x*(218 - 1627*x + 5364*x^2 - 10163*x^3 + 12093*x^4 - 9259*x^5 + 4469*x^6 - 1253*x^7 + 160*x^8) /
((1 - x)^8*(1 - 2*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (2 * PowerSeries.X * (218 - 1627 * PowerSeries.X + 5364 * PowerSeries.X ^ 2 - 10163 * PowerSeries.X ^ 3 + 12093 * PowerSeries.X ^ 4 - 9259 * PowerSeries.X ^ 5 + 4469 * PowerSeries.X ^ 6 - 1253 * PowerSeries.X ^ 7 + 160 * PowerSeries.X ^ 8)) * ((1 - PowerSeries.X) ^ 8 * (1 - 2 * PowerSeries.X))⁻¹

/-- The empirical recurrence (n ≥ 10), the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 44 * (a (n - 2) : ℤ) + 112 * (a (n - 3) : ℤ) - 182 * (a (n - 4) : ℤ) + 196 * (a (n - 5) : ℤ) - 140 * (a (n - 6) : ℤ) + 64 * (a (n - 7) : ℤ) - 17 * (a (n - 8) : ℤ) + 2 * (a (n - 9) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2520 * (289 * (2 : ℚ) ^ n - 209) - 314796 * (n : ℚ) - 41972 * (n : ℚ) ^ 2 - 23779 * (n : ℚ) ^ 3 + 385 * (n : ℚ) ^ 4 - 364 * (n : ℚ) ^ 5 + 7 * (n : ℚ) ^ 6 - (n : ℚ) ^ 7) / 1260) := by
  sorry

end OMA.S_oeis_a250781
