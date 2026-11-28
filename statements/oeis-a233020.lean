import Mathlib

/-!
# A233020: Number of n X 2 0..3 arrays with no element x(i,j) adjacent to value 3-x(i,j) horizontally, vertically, diagonally or antidiagonally, and top left element zero

Source: https://oeis.org/A233020
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 3, 15, 81, 435, 2337, 12555, ...). An array is a map
x : Fin n → Fin 2 → Fin 4 (row i, column j, value in 0..3). Two different cells (i,j), (i',j') are
adjacent horizontally, vertically, diagonally or antidiagonally when |i - i'| ≤ 1 and |j - j'| ≤ 1.
The condition is that x(i',j') ≠ 3 - x(i,j) for all adjacent cells, and x(0,0) = 0.

Conjectures (Colin Barker, Oct 06 2018), together with the empirical recurrence of the entry:
a(n) = 5*a(n-1) + 2*a(n-2) (stated for n ≥ 3, all indices at least the offset 1);
G.f.: 3*x / (1 - 5*x - 2*x^2) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = sqrt(3/11)*(((5+sqrt(33))/2)^n - ((5-sqrt(33))/2)^n) = 3*A015535(n) for n ≥ 1, where A015535
is the expansion of x/(1 - 5*x - 2*x^2), i.e. A015535(0) = 0, A015535(1) = 1 and
A015535(n) = 5*A015535(n-1) + 2*A015535(n-2).
-/

namespace OMA.S_oeis_a233020

/-- Cells p, q of an n X 2 array are adjacent (horizontally, vertically, diagonally or
antidiagonally): different, with row and column indices differing by at most 1. -/
def Adj {n : ℕ} (p q : Fin n × Fin 2) : Prop :=
  p ≠ q ∧ (p.1 : ℕ) ≤ q.1 + 1 ∧ (q.1 : ℕ) ≤ p.1 + 1 ∧ (p.2 : ℕ) ≤ q.2 + 1 ∧ (q.2 : ℕ) ≤ p.2 + 1

/-- No element is adjacent to 3 minus itself, and the top left element is zero. -/
def Good {n : ℕ} (x : Fin n → Fin 2 → Fin 4) : Prop :=
  (∀ p q : Fin n × Fin 2, Adj p q → (x q.1 q.2 : ℕ) ≠ 3 - (x p.1 p.2 : ℕ)) ∧
    ∀ h : 0 < n, x ⟨0, h⟩ 0 = 0

/-- a(n): the number of such n X 2 arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin n → Fin 2 → Fin 4 // Good x}

/-- A015535: b(0) = 0, b(1) = 1, b(n) = 5*b(n-1) + 2*b(n-2). -/
def b : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) + 2 * b n

/-- The conjectured g.f. 3*x / (1 - 5*x - 2*x^2). -/
noncomputable def G : PowerSeries ℚ :=
  (3 * PowerSeries.X) * (1 - 5 * PowerSeries.X - 2 * PowerSeries.X ^ 2)⁻¹

/-- The recurrence, the g.f., the closed form and a(n) = 3*A015535(n). -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 5 * a (n - 1) + 2 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = Real.sqrt (3 / 11) *
      (((5 + Real.sqrt 33) / 2) ^ n - ((5 - Real.sqrt 33) / 2) ^ n)) ∧
    (∀ n : ℕ, 1 ≤ n → a n = 3 * b n) := by
  sorry

end OMA.S_oeis_a233020
