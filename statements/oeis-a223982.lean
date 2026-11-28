import Mathlib

/-!
# A223982: Number of n X 3 0..3 arrays with rows unimodal and columns nondecreasing

Source: https://oeis.org/A223982
Credit: @ivillar

Status: open conjecture (R. H. Hardin's empirical formula, Mar 30 2013; g.f. and recurrence
conjectured by Colin Barker, Aug 25 2018).

R. H. Hardin's sequence (offset 1, data 50, 684, 5029, 25410, 99634, 325120, ...). An array is a map
x : Fin n → Fin 3 → Fin 4 (row i, column j, entries 0..3). Every row x i is unimodal (weakly
increasing, then weakly decreasing; see Unimodal) and every column i ↦ x i j is nondecreasing. a(n)
is the number of such arrays.

Conjectures of the entry, all three stated in `main`:
a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) -
45*a(n-8) + 10*a(n-9) - a(n-10) for n>10 (stated for n ≥ 11, so that all indices are at least the
offset 1; over ℤ);
G.f.: x*(50 + 184*x + 439*x^2 - 100*x^3 + 259*x^4 - 210*x^5 + 120*x^6 - 45*x^7 + 10*x^8 - x^9) / (1
- x)^10 (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (353/181440)*n^9 + (5/126)*n^8 + (10571/30240)*n^7 + (251/144)*n^6 + (46793/8640)*n^5 +
(1565/144)*n^4 + (159679/11340)*n^3 + (715/63)*n^2 + (6491/1260)*n + 1 (n ≥ 1, over ℚ).
-/

namespace OMA.S_oeis_a223982

/-- A row r is unimodal: it is nondecreasing up to some position p and nonincreasing from p on. -/
def Unimodal (r : Fin 3 → Fin 4) : Prop :=
  ∃ p : Fin 3, (∀ i j : Fin 3, i ≤ j → j ≤ p → r i ≤ r j) ∧ (∀ i j : Fin 3, p ≤ i → i ≤ j → r j ≤ r i)

/-- a(n): the number of n X 3 arrays x (row i, column j, entries 0..3) with every row unimodal and every column
nondecreasing (downwards). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 3 → Fin 4 // (∀ i, Unimodal (x i)) ∧ ∀ j, Monotone (fun i => x i j)}

/-- The conjectured g.f. x*(50 + 184*x + 439*x^2 - 100*x^3 + 259*x^4 - 210*x^5 + 120*x^6 - 45*x^7 + 10*x^8 - x^9) / (1 - x)^10. -/
noncomputable def G : PowerSeries ℚ :=
  (50 * PowerSeries.X + 184 * PowerSeries.X ^ 2 + 439 * PowerSeries.X ^ 3 - 100 * PowerSeries.X ^ 4 + 259 * PowerSeries.X ^ 5 - 210 * PowerSeries.X ^ 6 + 120 * PowerSeries.X ^ 7 - 45 * PowerSeries.X ^ 8 + 10 * PowerSeries.X ^ 9 - 1 * PowerSeries.X ^ 10) * ((1 - PowerSeries.X) ^ 10)⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 11 ≤ n → (a n : ℤ) = 10 * (a (n - 1) : ℤ) - 45 * (a (n - 2) : ℤ) + 120 * (a (n - 3) : ℤ) - 210 * (a (n - 4) : ℤ) + 252 * (a (n - 5) : ℤ) - 210 * (a (n - 6) : ℤ) + 120 * (a (n - 7) : ℤ) - 45 * (a (n - 8) : ℤ) + 10 * (a (n - 9) : ℤ) - 1 * (a (n - 10) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1 : ℚ) + (6491/1260 : ℚ) * (n : ℚ) + (715/63 : ℚ) * (n : ℚ) ^ 2 + (159679/11340 : ℚ) * (n : ℚ) ^ 3 + (1565/144 : ℚ) * (n : ℚ) ^ 4 + (46793/8640 : ℚ) * (n : ℚ) ^ 5 + (251/144 : ℚ) * (n : ℚ) ^ 6 + (10571/30240 : ℚ) * (n : ℚ) ^ 7 + (5/126 : ℚ) * (n : ℚ) ^ 8 + (353/181440 : ℚ) * (n : ℚ) ^ 9) := by
  sorry

end OMA.S_oeis_a223982
