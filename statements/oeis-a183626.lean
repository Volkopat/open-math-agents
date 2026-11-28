import Mathlib

/-!
# A183626: Number of (n+1) X 4 0..2 arrays with every 2 X 2 subblock summing to 4

Source: https://oeis.org/A183626
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 115, 189, 355, 741, 1675, 4029, ...). An array is a map
x : Fin (n+1) → Fin 4 → Fin 3 (row i, column j, value in 0..2); its 2 X 2 subblocks are formed by
rows i, i+1 and columns j, j+1, and the four entries of each must sum to 4.

Conjectures (Colin Barker, Mar 30 2018), together with the empirical recurrence of the entry:
a(n) = 6*a(n-1) - 11*a(n-2) + 6*a(n-3) (stated for n ≥ 4, all indices at least the offset 1, over ℤ);
G.f.: x*(115 - 501*x + 486*x^2) / ((1 - x)*(1 - 2*x)*(1 - 3*x)) (of Sum_{n ≥ 1} a(n) x^n, over ℚ);
a(n) = 50 + 7*2^(2+n) + 3^(1+n) (n ≥ 1).
-/

namespace OMA.S_oeis_a183626

/-- All three 2 X 2 subblocks formed by rows u, v sum to 4. -/
def BlockOK (u v : Fin 4 → Fin 3) : Prop :=
  ∀ j : Fin 3, (u j.castSucc : ℕ) + u j.succ + v j.castSucc + v j.succ = 4

/-- a(n): the number of such (n+1) X 4 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 4 → Fin 3 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- The conjectured g.f. x*(115 - 501*x + 486*x^2) / ((1 - x)*(1 - 2*x)*(1 - 3*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (115 - 501 * PowerSeries.X + 486 * PowerSeries.X ^ 2)) *
    ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 11 * a (n - 2) + 6 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → a n = 50 + 7 * 2 ^ (2 + n) + 3 ^ (1 + n)) := by
  sorry

end OMA.S_oeis_a183626
