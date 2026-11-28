import Mathlib

/-!
# A250895: Number of (n+1) X (5+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction

Source: https://oeis.org/A250895
Credit: @ivillar

Status: open conjecture (empirical recurrence of R. H. Hardin, Nov 28 2014; g.f. and closed form conjectured by Colin Barker, Nov 23 2018); a proof is filed with this statement.

R. H. Hardin's sequence (offset 1, data 3673, 11029, 33821, 102789, 305429, 890199, ...). An array is a map
x : Fin (n + 1) → Fin 6 → Fin 3 (row i, column j, value in 0..2).
The two conditions concern every 2 X 2 subblock, with rows i, i+1, columns j, j+1 and entries
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1):
* x(i,j)-x(i,j-1) is nondecreasing in the i direction: q - p ≤ s - r;
* the absolute value of x(i,j)-x(i-1,j) is nondecreasing in the j direction: |r - p| ≤ |s - q|.

Conjectures of the entry:
* Empirical (Hardin): a(n) = 12*a(n-1) - 60*a(n-2) + 162*a(n-3) - 255*a(n-4) + 234*a(n-5)
  - 116*a(n-6) + 24*a(n-7) for n>9 (over ℤ);
* G.f. (Barker): x*(3673 - 33047*x + 121853*x^2 - 236349*x^3 + 251138*x^4 - 133698*x^5 + 14708*x^6
  + 21650*x^7 - 8800*x^8) / ((1 - x)^3*(1 - 2*x)^3*(1 - 3*x)) (of Sum_{n ≥ 1} a(n) x^n, as a power
  series over ℚ);
* a(n) = -877 + 1553*2^(-3+n) + 17956*3^(-3+n) + (976-2779*2^(-4+n))*n + (282+3087*2^(-4+n))*n^2
  for n>2 (Barker; over ℚ, the powers with integer exponents -3+n and -4+n).
-/

namespace OMA.S_oeis_a250895

/-- The condition on a 2 X 2 subblock with upper row (p, q) and lower row (r, s), i.e.
p = x(i,j), q = x(i,j+1), r = x(i+1,j), s = x(i+1,j+1). -/
def CellOK (p q r s : ℤ) : Prop := q - p ≤ s - r ∧ (r - p).natAbs ≤ (s - q).natAbs

/-- a(n): the number of (n+1) X 6 arrays with entries in 0..2 all of whose 2 X 2 subblocks satisfy
the condition. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 6 → Fin 3 // ∀ i : Fin n, ∀ j : Fin 5,
    CellOK ((x i.castSucc j.castSucc : ℕ) : ℤ) ((x i.castSucc j.succ : ℕ) : ℤ) ((x i.succ j.castSucc : ℕ) : ℤ) ((x i.succ j.succ : ℕ) : ℤ)}

/-- The conjectured g.f. x*(3673 - 33047*x + 121853*x^2 - 236349*x^3 + 251138*x^4 - 133698*x^5 + 14708*x^6 + 21650*x^7 - 8800*x^8) / ((1 - x)^3*(1 - 2*x)^3*(1 - 3*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (3673 - 33047 * PowerSeries.X + 121853 * PowerSeries.X ^ 2 - 236349 * PowerSeries.X ^ 3 + 251138 * PowerSeries.X ^ 4 - 133698 * PowerSeries.X ^ 5 + 14708 * PowerSeries.X ^ 6 + 21650 * PowerSeries.X ^ 7 - 8800 * PowerSeries.X ^ 8)) * ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X) ^ 3 * (1 - 3 * PowerSeries.X))⁻¹

/-- The empirical recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 12 * a (n - 1) - 60 * a (n - 2) + 162 * a (n - 3) - 255 * a (n - 4) + 234 * a (n - 5) - 116 * a (n - 6) + 24 * a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = -877 + 1553 * (2 : ℚ) ^ (-3 + (n : ℤ)) + 17956 * (3 : ℚ) ^ (-3 + (n : ℤ)) + (976 - 2779 * (2 : ℚ) ^ (-4 + (n : ℤ))) * (n : ℚ) + (282 + 3087 * (2 : ℚ) ^ (-4 + (n : ℤ))) * (n : ℚ) ^ 2) := by
  sorry

end OMA.S_oeis_a250895
