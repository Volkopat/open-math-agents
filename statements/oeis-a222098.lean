import Mathlib

/-!
# A222098: Number of n X 2 0..5 arrays with entries increasing mod 6 by 0, 1, 2 or 3 rightwards and downwards, starting with upper left zero

Source: https://oeis.org/A222098
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 4, 46, 530, 6108, 70394, ...). An array is a map
x : Fin n → Fin 2 → Fin 6 (row i, column j, value in 0..5). Moving one step rightwards (column j to
j+1) or downwards (row i to i+1), the entry increases mod 6 by 0, 1, 2 or 3, i.e. the difference
taken in ZMod 6 (Fin 6 subtraction) is at most 3; and the upper left entry is 0.

Conjectures (Colin Barker, Aug 15 2018), together with the empirical recurrence of the entry:
a(n) = 13*a(n-1) - 17*a(n-2) (stated for n ≥ 3, all indices at least the offset 1, over ℤ);
G.f.: 2*x*(2 - 3*x) / (1 - 13*x + 17*x^2) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (2^(-n)*((13-sqrt(101))^n*(-29+3*sqrt(101)) + (13+sqrt(101))^n*(29+3*sqrt(101))))
  / (17*sqrt(101)) (n ≥ 1, over ℝ).
-/

namespace OMA.S_oeis_a222098

/-- The conditions: rightward and downward steps increase the entry by 0..3 mod 6, and the upper left
entry is zero. -/
def Good {n : ℕ} (x : Fin n → Fin 2 → Fin 6) : Prop :=
  (∀ (i : Fin n) (j j' : Fin 2), (j' : ℕ) = j + 1 → ((x i j' - x i j : Fin 6) : ℕ) ≤ 3) ∧
  (∀ (i i' : Fin n) (j : Fin 2), (i' : ℕ) = i + 1 → ((x i' j - x i j : Fin 6) : ℕ) ≤ 3) ∧
  ∀ h : 0 < n, x ⟨0, h⟩ 0 = 0

/-- a(n): the number of such n X 2 arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin n → Fin 2 → Fin 6 // Good x}

/-- The conjectured g.f. 2*x*(2 - 3*x) / (1 - 13*x + 17*x^2). -/
noncomputable def G : PowerSeries ℚ :=
  (2 * PowerSeries.X * (2 - 3 * PowerSeries.X)) *
    (1 - 13 * PowerSeries.X + 17 * PowerSeries.X ^ 2)⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 13 * a (n - 1) - 17 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (2 : ℝ) ^ (-(n : ℤ)) *
      ((13 - Real.sqrt 101) ^ n * (-29 + 3 * Real.sqrt 101) +
        (13 + Real.sqrt 101) ^ n * (29 + 3 * Real.sqrt 101)) / (17 * Real.sqrt 101)) := by
  sorry

end OMA.S_oeis_a222098
