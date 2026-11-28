import Mathlib

/-!
# OEIS A239171: Barker's g.f. and closed form for (n+1) X 2 0..2 arrays, no element above its row neighbor or equal to all vertical neighbors

Source: https://oeis.org/A239171 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A239171 (R. H. Hardin, Mar 11 2014), offset 1: Number of (n+1) X (1+1) 0..2 arrays with no element
greater than all horizontal neighbors or equal to all vertical neighbors. Column 1 of A239178.
Formula section:
Conjectures from Colin Barker, Oct 25 2018:
G.f.: 6*x / (1 - 2*x - 2*x^2).
a(n) = sqrt(3)*((1+sqrt(3))^n-(1-sqrt(3))^n).

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 2 -> Fin 3, x i j being the element in row i and
  column j. The horizontal neighbors of (i, j) are the elements (i, j') with j' = j + 1 or
  j = j' + 1, and the vertical neighbors are the elements (i', j) with i' = i + 1 or i = i' + 1.
* An element is greater than all its horizontal neighbors when every horizontal neighbor is
  smaller than it, and equal to all its vertical neighbors when every vertical neighbor has its
  value; `good` excludes both for every element. With two columns every element has exactly one
  horizontal neighbor, and with n + 1 >= 2 rows at least one vertical neighbor, so neither
  condition is vacuous for n >= 1.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity
  A(x) (1 - 2x - 2x^2) = 6x in the formal power series ring over the rationals, with
  A(x) = Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the
  reals for every n >= 1.
* Controls proved in the proof file: the definition gives 6, 12, 36, 96, 264, 720, 1968, 5376, 14688, 40128, 109632, 299520 for n = 1..12, the entry's
  data (from the proved recurrence and a(1), a(2), a(3)), and a direct enumeration of all arrays
  with three rows gives a(2) = 12.
-/

namespace OMA.S_oeis_a239171

open PowerSeries Finset

/-- Columns j and j' of a 2-column array are horizontal neighbors. -/
def hnb (j j' : Fin 2) : Prop := j.val + 1 = j'.val ∨ j'.val + 1 = j.val

/-- Rows i and i' are vertical neighbors. -/
def vnb {m : ℕ} (i i' : Fin m) : Prop := i.val + 1 = i'.val ∨ i'.val + 1 = i.val

instance : DecidableRel hnb := fun j j' => by unfold hnb; infer_instance

instance {m : ℕ} : DecidableRel (@vnb m) := fun i i' => by unfold vnb; infer_instance

/-- No element of the array x (row i, column j) is greater than all its horizontal neighbors, and
no element is equal to all its vertical neighbors. -/
def good {m : ℕ} (x : Fin m → Fin 2 → Fin 3) : Prop :=
  ∀ i j, ¬ (∀ j', hnb j j' → x i j' < x i j) ∧ ¬ (∀ i', vnb i i' → x i' j = x i j)

instance {m : ℕ} : DecidablePred (@good m) := fun x => by unfold good; infer_instance

/-- A239171(n): the number of (n+1) X 2 arrays with entries 0..2 satisfying `good`. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 3)).filter good).card

/-- Barker's conjectures: the g.f. 6x/(1 - 2x - 2x^2) and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 2 * X - 2 * X ^ 2) = 6 * X ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      Real.sqrt 3 * ((1 + Real.sqrt 3) ^ n - (1 - Real.sqrt 3) ^ n) := by
  sorry

end OMA.S_oeis_a239171
