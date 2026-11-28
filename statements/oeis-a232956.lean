import Mathlib

/-!
# A232956: Number of 2 X n 0..3 arrays with no element x(i,j) adjacent to value 3-x(i,j) horizontally, diagonally or antidiagonally, and top left element zero

Source: https://oeis.org/A232956
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 4, 21, 129, 771, 4629, 27771, ...). An array is a map
x : Fin 2 → Fin n → Fin 4 (row i, column j, value in 0..3). Cells (i,j), (i',j') are adjacent
horizontally, diagonally or antidiagonally when |i - i'| ≤ 1 and |j - j'| = 1 (vertical neighbours,
in the same column, are not constrained). The condition is that x(i',j') ≠ 3 - x(i,j) for all such
adjacent cells, and x(0,0) = 0.

Conjectures (Colin Barker, Oct 06 2018), together with the empirical recurrence of the entry:
a(n) = 5*a(n-1) + 6*a(n-2) (stated for n ≥ 3, all indices at least the offset 1);
G.f.: x*(4 + x) / ((1 + x)*(1 - 6*x)) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = (25*6^n - 18) / 42 for n even, a(n) = (25*6^n + 18) / 42 for n odd (n ≥ 1, over ℚ).
-/

namespace OMA.S_oeis_a232956

/-- Cells p, q of a 2 X n array are adjacent horizontally, diagonally or antidiagonally: row
indices differ by at most 1 and column indices differ by exactly 1. -/
def Adj {n : ℕ} (p q : Fin 2 × Fin n) : Prop :=
  (p.1 : ℕ) ≤ q.1 + 1 ∧ (q.1 : ℕ) ≤ p.1 + 1 ∧ ((p.2 : ℕ) = q.2 + 1 ∨ (q.2 : ℕ) = p.2 + 1)

/-- No element is adjacent to 3 minus itself, and the top left element is zero. -/
def Good {n : ℕ} (x : Fin 2 → Fin n → Fin 4) : Prop :=
  (∀ p q : Fin 2 × Fin n, Adj p q → (x q.1 q.2 : ℕ) ≠ 3 - (x p.1 p.2 : ℕ)) ∧
    ∀ h : 0 < n, x 0 ⟨0, h⟩ = 0

/-- a(n): the number of such 2 X n arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin 2 → Fin n → Fin 4 // Good x}

/-- The conjectured g.f. x*(4 + x) / ((1 + x)*(1 - 6*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (4 + PowerSeries.X)) * ((1 + PowerSeries.X) * (1 - 6 * PowerSeries.X))⁻¹

/-- The recurrence, the g.f. and the closed forms. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 5 * a (n - 1) + 6 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = (25 * 6 ^ n - 18) / 42) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = (25 * 6 ^ n + 18) / 42) := by
  sorry

end OMA.S_oeis_a232956
