import Mathlib

/-!
# A183702: Number of (n+1) X 2 0..3 arrays with every 2 X 2 subblock nonsingular

Source: https://oeis.org/A183702
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 192, 2472, 31800, 409128, 5263608, ...). An array is a map
x : Fin (n+1) → Fin 2 → Fin 4 (row i, column j, value in 0..3); its 2 X 2 subblocks are formed
by rows i, i+1, and the subblock [[p, q], [r, s]] is nonsingular when its determinant p*s - q*r
(an integer) is nonzero.

Conjectures (Colin Barker, Apr 04 2018), together with the empirical recurrence of the entry:
a(n) = 11*a(n-1) + 24*a(n-2) (stated for n ≥ 3, all indices at least the offset 1);
G.f.: 24*x*(8 + 15*x) / (1 - 11*x - 24*x^2) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (3*2^(-1-n)*((11-sqrt(217))^n*(-73+5*sqrt(217)) + (11+sqrt(217))^n*(73+5*sqrt(217)))) / sqrt(217) (n ≥ 1, over ℝ).
-/

namespace OMA.S_oeis_a183702

/-- The subblock formed by rows u, v is nonsingular. -/
def BlockOK (u v : Fin 2 → Fin 4) : Prop := (u 0 : ℤ) * (v 1 : ℤ) - (u 1 : ℤ) * (v 0 : ℤ) ≠ 0

/-- a(n): the number of (n+1) X 2 arrays over 0..3 all of whose 2 X 2 subblocks are nonsingular. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 2 → Fin 4 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- The conjectured g.f. 24*x*(8 + 15*x) / (1 - 11*x - 24*x^2). -/
noncomputable def G : PowerSeries ℚ :=
  (24 * PowerSeries.X * (8 + 15 * PowerSeries.X)) * (1 - 11 * PowerSeries.X - 24 * PowerSeries.X ^ 2)⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 11 * a (n - 1) + 24 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 3 * (2 : ℝ) ^ ((-1 : ℤ) - n) * ((11 - Real.sqrt 217) ^ n * (-73 + 5 * Real.sqrt 217) +
        (11 + Real.sqrt 217) ^ n * (73 + 5 * Real.sqrt 217)) / Real.sqrt 217) := by
  sorry

end OMA.S_oeis_a183702
