import Mathlib

/-!
# OEIS A208641: Barker's generating function and closed form

Source: https://oeis.org/A208641 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.
No human mathematician has reviewed this translation; please review it as strictly as any other.

Entry (R. H. Hardin, Feb 29 2012), offset 1: Number of 6 X n 0..1 arrays with new values 0..1 introduced in row major order and no element equal to more than one of its immediate leftward or upward or right-upward antidiagonal neighbors.
Data: 32, 233, 851, 2331, 5572, 12404, ... Formula section: Conjectures from Colin Barker, Jul 05 2018:
G.f.: x*(32 + 9*x - 140*x^2 + 74*x^3 + 85*x^4 - 37*x^5 - 34*x^6 + 4*x^7 + 8*x^8) / ((1 - x)^5*(1 - 2*x)). a(n) = (792*(7*2^n-10) - 3382*n - 539*n^2 - 38*n^3 - n^4) / 24 for n>3.

Formalization notes:
* A 6 X n array with entries 0..1 is a map `x : Fin 6 → Fin n → Fin 2`, with x(i,j) = `x i j`:
  row i (numbered from the top) and column j (numbered from the left).
* The immediate leftward neighbour of x(i,j) is x(i,j-1), its upward neighbour is x(i-1,j) and its
  right-upward antidiagonal neighbour is x(i-1,j+1); a neighbour that falls outside the array does
  not exist. `eqLeft x i j`, `eqUp x i j`, `eqRightUp x i j` say that the neighbour exists and is
  equal to x(i,j). "No element equal to more than one of" these neighbours means that for every
  element at most one of the three holds (`fewEqual`).
* "New values 0..1 introduced in row major order": the values first appear in the order 0, 1 when
  the array is read row by row from the top, each row from the left; for entries 0..1 this says
  that every 1 is preceded, in row major order, by a 0 (`newInOrder`). Arrays that contain no 1
  qualify.
* This reading reproduces every listed term of the entry by a transfer-matrix computation, and
  a(1), a(2), a(3) by direct enumeration of all arrays against the entry's wording.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the rationals for
  n >= 4. `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a208641

open PowerSeries

/-- The element x(i,j) has a leftward neighbour x(i,j-1), equal to it. -/
def eqLeft {n : ℕ} (x : Fin 6 → Fin n → Fin 2) (i : Fin 6) (j : Fin n) : Prop :=
  ∃ j' : Fin n, j'.val + 1 = j.val ∧ x i j' = x i j

/-- The element x(i,j) has an upward neighbour x(i-1,j), equal to it. -/
def eqUp {n : ℕ} (x : Fin 6 → Fin n → Fin 2) (i : Fin 6) (j : Fin n) : Prop :=
  ∃ i' : Fin 6, i'.val + 1 = i.val ∧ x i' j = x i j

/-- The element x(i,j) has a right-upward antidiagonal neighbour x(i-1,j+1), equal to it. -/
def eqRightUp {n : ℕ} (x : Fin 6 → Fin n → Fin 2) (i : Fin 6) (j : Fin n) : Prop :=
  ∃ i' : Fin 6, ∃ j' : Fin n, i'.val + 1 = i.val ∧ j'.val = j.val + 1 ∧ x i' j' = x i j

/-- No element is equal to more than one of its leftward, upward and right-upward antidiagonal
neighbours. -/
def fewEqual {n : ℕ} (x : Fin 6 → Fin n → Fin 2) : Prop :=
  ∀ i j, ¬ (eqLeft x i j ∧ eqUp x i j) ∧ ¬ (eqLeft x i j ∧ eqRightUp x i j) ∧
    ¬ (eqUp x i j ∧ eqRightUp x i j)

/-- New values are introduced in row major order: every 1 is preceded, in row major order, by a 0. -/
def newInOrder {n : ℕ} (x : Fin 6 → Fin n → Fin 2) : Prop :=
  ∀ i j, x i j = 1 → ∃ i' j', (i'.val < i.val ∨ (i' = i ∧ j'.val < j.val)) ∧ x i' j' = 0

instance {n : ℕ} (x : Fin 6 → Fin n → Fin 2) : Decidable (fewEqual x) := by
  unfold fewEqual eqLeft eqUp eqRightUp; infer_instance

instance {n : ℕ} (x : Fin 6 → Fin n → Fin 2) : Decidable (newInOrder x) := by
  unfold newInOrder; infer_instance

/-- A208641(n): the number of 6 X n arrays with entries 0..1 satisfying both conditions. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin 6 → Fin n → Fin 2 => newInOrder x ∧ fewEqual x).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n >= 4. -/
theorem main :
    gf = X * (32 + 9 * X - 140 * X ^ 2 + 74 * X ^ 3 + 85 * X ^ 4 - 37 * X ^ 5 - 34 * X ^ 6 + 4 * X ^ 7 + 8 * X ^ 8) * ((1 - X) ^ 5 * (1 - 2 * X))⁻¹ ∧
    ∀ n : ℕ, 4 ≤ n → (a n : ℚ) = (792 * (7 * 2 ^ n - 10) - 3382 * n - 539 * n ^ 2 - 38 * n ^ 3 - n ^ 4) / 24 := by
  sorry

end OMA.S_oeis_a208641
