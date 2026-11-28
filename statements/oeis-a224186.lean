import Mathlib

/-!
# A224186: Number of n X 4 0..2 arrays with rows unimodal and columns nondecreasing

Source: https://oeis.org/A224186
Credit: @ivillar

Status: open conjecture (R. H. Hardin's empirical formula, Apr 01 2013; g.f. and recurrence
conjectured by Colin Barker, Aug 29 2018).

R. H. Hardin's sequence (offset 1, data 46, 548, 3526, 15779, 55438, 163746, ...). An array is a map
x : Fin n → Fin 4 → Fin 3 (row i, column j, entries 0..2). Every row x i is unimodal (weakly
increasing, then weakly decreasing; see Unimodal) and every column i ↦ x i j is nondecreasing. a(n)
is the number of such arrays.

Conjectures of the entry, all three stated in `main`:
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8)
+ a(n-9) for n>9 (stated for n ≥ 10, so that all indices are at least the offset 1; over ℤ);
G.f.: x*(46 + 134*x + 250*x^2 - 91*x^3 + 127*x^4 - 84*x^5 + 36*x^6 - 9*x^7 + x^8) / (1 - x)^9 (of
Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (41/4032)*n^8 + (55/336)*n^7 + (179/160)*n^6 + (169/40)*n^5 + (615/64)*n^4 + (215/16)*n^3 +
(56759/5040)*n^2 + (2173/420)*n + 1 (n ≥ 1, over ℚ).
-/

namespace OMA.S_oeis_a224186

/-- A row r is unimodal: it is nondecreasing up to some position p and nonincreasing from p on. -/
def Unimodal (r : Fin 4 → Fin 3) : Prop :=
  ∃ p : Fin 4, (∀ i j : Fin 4, i ≤ j → j ≤ p → r i ≤ r j) ∧ (∀ i j : Fin 4, p ≤ i → i ≤ j → r j ≤ r i)

/-- a(n): the number of n X 4 arrays x (row i, column j, entries 0..2) with every row unimodal and every column
nondecreasing (downwards). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 4 → Fin 3 // (∀ i, Unimodal (x i)) ∧ ∀ j, Monotone (fun i => x i j)}

/-- The conjectured g.f. x*(46 + 134*x + 250*x^2 - 91*x^3 + 127*x^4 - 84*x^5 + 36*x^6 - 9*x^7 + x^8) / (1 - x)^9. -/
noncomputable def G : PowerSeries ℚ :=
  (46 * PowerSeries.X + 134 * PowerSeries.X ^ 2 + 250 * PowerSeries.X ^ 3 - 91 * PowerSeries.X ^ 4 + 127 * PowerSeries.X ^ 5 - 84 * PowerSeries.X ^ 6 + 36 * PowerSeries.X ^ 7 - 9 * PowerSeries.X ^ 8 + 1 * PowerSeries.X ^ 9) * ((1 - PowerSeries.X) ^ 9)⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 9 * (a (n - 1) : ℤ) - 36 * (a (n - 2) : ℤ) + 84 * (a (n - 3) : ℤ) - 126 * (a (n - 4) : ℤ) + 126 * (a (n - 5) : ℤ) - 84 * (a (n - 6) : ℤ) + 36 * (a (n - 7) : ℤ) - 9 * (a (n - 8) : ℤ) + 1 * (a (n - 9) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1 : ℚ) + (2173/420 : ℚ) * (n : ℚ) + (56759/5040 : ℚ) * (n : ℚ) ^ 2 + (215/16 : ℚ) * (n : ℚ) ^ 3 + (615/64 : ℚ) * (n : ℚ) ^ 4 + (169/40 : ℚ) * (n : ℚ) ^ 5 + (179/160 : ℚ) * (n : ℚ) ^ 6 + (55/336 : ℚ) * (n : ℚ) ^ 7 + (41/4032 : ℚ) * (n : ℚ) ^ 8) := by
  sorry

end OMA.S_oeis_a224186
