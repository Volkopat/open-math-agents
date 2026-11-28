import Mathlib

/-!
# OEIS A231104: Barker's generating function and closed form

Source: https://oeis.org/A231104 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.
No human mathematician has reviewed this translation; please review it as strictly as any other.

Entry (R. H. Hardin, Nov 03 2013), offset 1: Number of n X 4 0..3 arrays x(i,j) with each element
horizontally or antidiagonally next to at least one element with value (x(i,j)+1) mod 4, no
adjacent elements equal, and upper left element zero. Data: 0, 6, 48, 438, 3936, 35430, 318864,
... Formula section: Empirical: a(n) = 8*a(n-1) + 9*a(n-2). Conjectures from Colin Barker,
Sep 26 2018: G.f.: 6*x^2 / ((1 + x)*(1 - 9*x)). a(n) = (9^n + 9) / 15 for n even.
a(n) = (9^n - 9) / 15 for n odd.

Formalization notes:
* An n X 4 array with entries 0..3 is a map `x : Fin n → Fin 4 → Fin 4`, with x(i,j) = `x i j`:
  row i is the map `x i`, rows are numbered from the top and columns from the left. Addition in
  `Fin 4` is modulo 4, so `v + 1` is (v+1) mod 4.
* The elements horizontally next to x(i,j) are x(i,j-1) and x(i,j+1); the elements antidiagonally
  next to it are x(i-1,j+1) (in the row above) and x(i+1,j-1) (in the row below), whenever these
  positions lie in the array. `cellOk above r below j` says that the element in column j of the
  row r has such a neighbour with value (r j + 1) mod 4, and that none of these neighbours is
  equal to it, where `above` and `below` are the rows directly above and below r (`none` at the
  top and bottom of the array).
* "Adjacent" in "no adjacent elements equal" is read with the same adjacency as the rest of the
  entry: horizontally or antidiagonally next to each other (vertically adjacent elements may be
  equal). This is the reading that reproduces the data; forbidding equal vertical neighbours as
  well gives a(2) = 2 instead of 6.
* `valid` asks this for every element, and that the upper left element x(0,0) is 0.
* This reading reproduces every listed term of the entry by a transfer-matrix computation, and
  a(1), a(2), a(3) by direct enumeration of all arrays against the entry's wording.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed forms are stated in the rationals for the
  terms of the sequence, n >= 1, split by parity. `main` is the conjunction of Barker's
  conjectures.
-/

namespace OMA.S_oeis_a231104

open PowerSeries

/-- The element in column j of the row r has, among its horizontal neighbours in r, its
antidiagonal neighbour in column j+1 of the row `above`, and its antidiagonal neighbour in column
j-1 of the row `below`, at least one with value (r j + 1) mod 4, and none equal to itself. -/
def cellOk (above : Option (Fin 4 → Fin 4)) (r : Fin 4 → Fin 4) (below : Option (Fin 4 → Fin 4))
    (j : Fin 4) : Prop :=
  ((∃ k : Fin 4, (k.val + 1 = j.val ∨ j.val + 1 = k.val) ∧ r k = r j + 1) ∨
    (∃ p : Fin 4 → Fin 4, above = some p ∧ ∃ k : Fin 4, k.val = j.val + 1 ∧ p k = r j + 1) ∨
    (∃ q : Fin 4 → Fin 4, below = some q ∧ ∃ k : Fin 4, k.val + 1 = j.val ∧ q k = r j + 1)) ∧
  (∀ k : Fin 4, (k.val + 1 = j.val ∨ j.val + 1 = k.val) → r k ≠ r j) ∧
  (∀ p : Fin 4 → Fin 4, above = some p → ∀ k : Fin 4, k.val = j.val + 1 → p k ≠ r j) ∧
  (∀ q : Fin 4 → Fin 4, below = some q → ∀ k : Fin 4, k.val + 1 = j.val → q k ≠ r j)

instance (above : Option (Fin 4 → Fin 4)) (r : Fin 4 → Fin 4) (below : Option (Fin 4 → Fin 4))
    (j : Fin 4) : Decidable (cellOk above r below j) := by
  unfold cellOk; infer_instance

/-- The row directly above row i of x (`none` for the top row). -/
def above {n : ℕ} (x : Fin n → Fin 4 → Fin 4) (i : Fin n) : Option (Fin 4 → Fin 4) :=
  if h : 0 < i.val then some (x ⟨i.val - 1, by omega⟩) else none

/-- The row directly below row i of x (`none` for the bottom row). -/
def below {n : ℕ} (x : Fin n → Fin 4 → Fin 4) (i : Fin n) : Option (Fin 4 → Fin 4) :=
  if h : i.val + 1 < n then some (x ⟨i.val + 1, h⟩) else none

/-- The upper left element is 0, and every element passes `cellOk`. -/
def valid {n : ℕ} (x : Fin n → Fin 4 → Fin 4) : Prop :=
  (∀ h : 0 < n, x ⟨0, h⟩ 0 = 0) ∧ ∀ i : Fin n, ∀ j : Fin 4, cellOk (above x i) (x i) (below x i) j

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 4) : Decidable (valid x) := by
  unfold valid; infer_instance

/-- A231104(n): the number of valid n X 4 arrays with entries 0..3. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 4 → Fin 4 => valid x).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed forms for n >= 1. -/
theorem main :
    gf = 6 * X ^ 2 * ((1 + X) * (1 - 9 * X))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n →
      (Even n → (a n : ℚ) = (9 ^ n + 9) / 15) ∧ (Odd n → (a n : ℚ) = (9 ^ n - 9) / 15) := by
  sorry

end OMA.S_oeis_a231104
