import Mathlib

/-!
# OEIS A233078: Barker's g.f. and closed form for n X 4 0..3 arrays with no element adjacent to 3 minus itself horizontally or antidiagonally, normalized

Source: https://oeis.org/A233078 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A233078 (R. H. Hardin, Dec 03 2013), offset 1: Number of n X 4 0..3 arrays with no element
x(i,j) adjacent to value 3-x(i,j) horizontally or antidiagonally, top left element zero, and 1
appearing before 2 in row major order. Column 4 of A233082.
Formula section:
Conjectures from Colin Barker, Oct 07 2018:
G.f.: 2*x*(7 - 19*x) / ((1 - x)*(1 - 49*x)).
a(n) = (49 + 27*49^n) / 98.

Formalization notes:
* An array is a function x : Fin n -> Fin 4 -> Fin 4, x i j being the entry in row i and column j.
* No element x(i,j) adjacent to value 3-x(i,j) horizontally or antidiagonally (`Cond`): for every
  pair of neighbors in these directions the two entries do not add up to 3. Horizontal neighbors are
  (i,j) and (i,j+1), antidiagonal neighbors (i,j) and (i+1,j-1); this reading reproduces the entry's
  data and its table's.
* Top left element zero, and 1 appearing before 2 in row major order (`Norm`): x(0,0) = 0, and
  every occurrence of a value listed after the word before has an occurrence of the value listed
  before it at an earlier position, reading the rows from the top and each row from the left. Values
  that do not occur impose nothing.
* The statement is the conjunction of Barker's two conjectures: the g.f. as the identity A(x) ((1
  - x)(1 - 49x)) = 2x(7 - 19x) in the formal power series ring over the rationals, with A(x) =
  Sum_{n >= 1} a(n) x^n (offset 1, so the constant term is 0), and the closed form in the rationals
  for every n >= 1.
* Controls proved in the proof file: the definition gives 14, 662, 32414, 1588262, 77824814,
  3813415862, 186857377214, 9156011483462, 448644562689614, 21983583571791062 for n = 1..10, the
  entry's data.
-/

namespace OMA.S_oeis_a233078

open PowerSeries Finset

/-- No element x(i,j) is adjacent to the value 3 - x(i,j) horizontally or antidiagonally: such
neighbors never add up to 3. -/
def Cond {R C : ℕ} (x : Fin R → Fin C → Fin 4) : Prop :=
  (∀ i j j', j'.val = j.val + 1 → (x i j).val + (x i j').val ≠ 3) ∧
    (∀ i i' j j', i'.val = i.val + 1 → j.val = j'.val + 1 → (x i j).val + (x i' j').val ≠ 3)

instance {R C : ℕ} : DecidablePred (@Cond R C) := fun x => by unfold Cond; infer_instance

/-- The top left element is zero, and 1 appears before 2 in row major order: every 2 has a 1 at an
earlier position (rows from the top, each row from the left). -/
def Norm {R C : ℕ} (x : Fin R → Fin C → Fin 4) : Prop :=
  (∀ i j, i.val = 0 → j.val = 0 → x i j = 0) ∧
    ∀ i j, x i j = 2 → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ x i' j' = 1

instance {R C : ℕ} : DecidablePred (@Norm R C) := fun x => by unfold Norm; infer_instance

/-- A233078(n): the number of n X 4 arrays with entries 0..3, x i j being the entry in row i and
column j, satisfying `Cond` and `Norm`. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 4 → Fin 4)).filter (fun x => Cond x ∧ Norm x)).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 49 * X)) = 2 * X * (7 - 19 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (49 + 27 * 49 ^ n) / 98 := by
  sorry

end OMA.S_oeis_a233078
