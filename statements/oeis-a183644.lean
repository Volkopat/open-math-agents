import Mathlib

/-!
# A183644: Number of (n+1) X 2 0..4 arrays with every 2 X 2 subblock summing to 8

Source: https://oeis.org/A183644
Credit: @ivillar

Status: known result: the entry records that Colin Barker's formulas below are correct (Jianing
Song, Jun 12 2026: the proof is similar to the one in A183654).

R. H. Hardin's sequence (offset 1, data 85, 325, 1333, 5725, 25405, ...). An array is a map
x : Fin (n+1) → Fin 2 → Fin 5 (row i, column j, value in 0..4); its 2 X 2 subblocks are formed by
rows i, i+1, and the four entries of each must sum to 8.

Formulas of the entry (empirical recurrence, and Colin Barker, Mar 31 2018):
a(n) = 15*a(n-1) - 85*a(n-2) + 225*a(n-3) - 274*a(n-4) + 120*a(n-5) (stated for n ≥ 6, all indices
at least the offset 1, over ℤ);
G.f.: x*(85 - 950*x + 3683*x^2 - 5770*x^3 + 3000*x^4) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)*(1 - 5*x))
(of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 2 + 2^(2+n) + 2^(3+2*n) + 2*3^(1+n) + 5^(1+n) (n ≥ 1).
-/

namespace OMA.S_oeis_a183644

/-- The subblock formed by rows u, v sums to 8. -/
def BlockOK (u v : Fin 2 → Fin 5) : Prop := (u 0 : ℕ) + u 1 + v 0 + v 1 = 8

/-- a(n): the number of such (n+1) X 2 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 2 → Fin 5 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- The g.f. of the entry. -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (85 - 950 * PowerSeries.X + 3683 * PowerSeries.X ^ 2 - 5770 * PowerSeries.X ^ 3 +
      3000 * PowerSeries.X ^ 4)) *
    ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) * (1 - 4 * PowerSeries.X) *
      (1 - 5 * PowerSeries.X))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 15 * a (n - 1) - 85 * a (n - 2) + 225 * a (n - 3) -
      274 * a (n - 4) + 120 * a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → a n = 2 + 2 ^ (2 + n) + 2 ^ (3 + 2 * n) + 2 * 3 ^ (1 + n) + 5 ^ (1 + n)) := by
  sorry

end OMA.S_oeis_a183644
