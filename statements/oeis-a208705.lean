import Mathlib

/-!
# A208705: Number of n X 4 0..1 arrays with new values 0..1 introduced in row major order and no element equal to more than two of its immediate leftward or upward or right-upward antidiagonal neighbors

Source: https://oeis.org/A208705
Credit: @ivillar

Status: open conjecture (empirical recurrence of R. H. Hardin, Mar 01 2012; g.f. and closed form conjectured by
Colin Barker, Jul 06 2018).

R. H. Hardin's sequence (offset 1, data 8, 100, 1268, 16084, 204020, 2587924, ...). An array is a map
x : Fin n → Fin 4 → Fin 2 (row i, column j). New values 0..1 introduced in row major order means that the
first element in row major order is 0, i.e. x(0,0) = 0. The immediate leftward neighbor of x(i,j) is
x(i,j-1), the upward neighbor is x(i-1,j) and the right-upward antidiagonal neighbor is x(i-1,j+1) (when
they exist); no element is equal to more than two of them, i.e. to all three, so the condition is:
not (x(i,j) = x(i,j-1) and x(i,j) = x(i-1,j) and x(i,j) = x(i-1,j+1)) for i ≥ 1 and 1 ≤ j ≤ 2.

Formulas of the entry, all formalized in `main`:
Empirical: a(n) = 13*a(n-1) - 4*a(n-2) (for n ≥ 3, all indices at least the offset 1);
G.f.: 4*x*(2 - x) / (1 - 13*x + 4*x^2) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (2^(-1-n)*((13-3*sqrt(17))^n*(-1+sqrt(17)) + (1+sqrt(17))*(13+3*sqrt(17))^n)) / sqrt(17) (n ≥ 1, over ℝ).
-/

namespace OMA.S_oeis_a208705

/-- Consecutive rows u (row i-1), v (row i): no element of v equals all three of its leftward, upward and
right-upward neighbors. -/
def BlockOK (u v : Fin 4 → Fin 2) : Prop :=
  ∀ j j' j'' : Fin 4, (j' : ℕ) = j + 1 → (j'' : ℕ) = j' + 1 → ¬ (v j' = v j ∧ v j' = u j' ∧ v j' = u j'')

/-- The first row starts with 0 (new values introduced in row major order). -/
def Init (u : Fin 4 → Fin 2) : Prop :=
  u 0 = 0

/-- The array conditions. -/
def Good {L : ℕ} (x : Fin L → Fin 4 → Fin 2) : Prop :=
  (∀ i j : Fin L, (j : ℕ) = i + 1 → BlockOK (x i) (x j)) ∧
    (∀ i : Fin L, (i : ℕ) = 0 → Init (x i))

/-- a(n): the number of such n X 4 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 4 → Fin 2 // Good x}

/-- The conjectured g.f. 4*x*(2 - x) / (1 - 13*x + 4*x^2). -/
noncomputable def G : PowerSeries ℚ :=
  (4 * PowerSeries.X * (2 - PowerSeries.X)) * (1 - 13 * PowerSeries.X + 4 * PowerSeries.X ^ 2)⁻¹

/-- The empirical recurrence (n ≥ 3), the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 13 * (a (n - 1) : ℤ) - 4 * (a (n - 2) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((2 : ℝ) ^ (-1 - (n : ℤ)) * ((13 - 3 * Real.sqrt 17) ^ n * (-1 + Real.sqrt 17) + (1 + Real.sqrt 17) * (13 + 3 * Real.sqrt 17) ^ n)) / Real.sqrt 17) := by
  sorry

end OMA.S_oeis_a208705
