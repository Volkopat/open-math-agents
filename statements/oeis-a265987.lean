import Mathlib

/-!
# OEIS A265987: Barker's generating function and closed form

Source: https://oeis.org/A265987 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of n X 3 integer arrays with each element equal to
the number of horizontal and antidiagonal neighbors not equal to itself.
Data: 2, 2, 6, 10, 30, 66, 182, 442, 1166, 2930, ...
Formula section: Conjectures from Colin Barker, Jan 09 2019:
G.f.: 2*x*(1 + x)*(1 - 2*x) / ((1 - x)*(1 - x - 4*x^2)).
a(n) = 1 + (-((1-sqrt(17))/2)^n + ((1+sqrt(17))/2)^n) / sqrt(17).

Formalization notes:
* An array is a function `A : Fin n → Fin 3 → ℤ` (row, then column).
* The horizontal neighbours of the element in row `i` and column `j` are the positions
  `(i, j - 1)` and `(i, j + 1)`, its antidiagonal neighbours are `(i - 1, j + 1)` and
  `(i + 1, j - 1)`; only positions inside the array count. `get A i j` is the entry at the
  integer position `(i, j)` (`none` outside the array), `differs A i j x` is 1 when that
  position is inside the array and holds a value different from `x` (0 otherwise), and
  `diffCount A i j` is the number of neighbours of `(i, j)` not equal to `A i j`.
  An array is valid when every element equals its `diffCount`. This reading reproduces all 29
  data terms of the entry.
* `a n` is the number of valid arrays, `Nat.card` of the subtype (the set is finite, since every
  entry of a valid array lies in 0..4).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a265987

open PowerSeries

/-- The entry of the array `A` at the integer position `(i, j)`, or `none` outside the array. -/
def get {n : ℕ} (A : Fin n → Fin 3 → ℤ) (i j : ℤ) : Option ℤ :=
  if h : 0 ≤ i ∧ i < n ∧ 0 ≤ j ∧ j < 3 then
    some (A ⟨i.toNat, by omega⟩ ⟨j.toNat, by omega⟩)
  else none

/-- `1` when the position `(i, j)` is inside the array and holds a value different from `x`,
and `0` otherwise. -/
def differs {n : ℕ} (A : Fin n → Fin 3 → ℤ) (i j x : ℤ) : ℕ :=
  match get A i j with
  | some y => if y = x then 0 else 1
  | none => 0

/-- The number of horizontal and antidiagonal neighbours of the element in row `i` and column
`j` (positions `(i, j - 1)`, `(i, j + 1)`, `(i - 1, j + 1)`, `(i + 1, j - 1)`) that are not
equal to it. -/
def diffCount {n : ℕ} (A : Fin n → Fin 3 → ℤ) (i : Fin n) (j : Fin 3) : ℕ :=
  differs A i (j - 1) (A i j) + differs A i (j + 1) (A i j) +
    differs A (i - 1) (j + 1) (A i j) + differs A (i + 1) (j - 1) (A i j)

/-- An `n × 3` integer array is valid when each element equals the number of its horizontal
and antidiagonal neighbours not equal to itself. -/
def valid (n : ℕ) (A : Fin n → Fin 3 → ℤ) : Prop :=
  ∀ (i : Fin n) (j : Fin 3), A i j = (diffCount A i j : ℤ)

/-- A265987(n): the number of valid `n × 3` integer arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin n → Fin 3 → ℤ // valid n A}

/-- Barker's conjectures for A265987 (offset 1): the generating function
2x(1 + x)(1 - 2x) / ((1 - x)(1 - x - 4x^2)), and the closed form for n >= 1. -/
theorem main :
    ((1 - X) * (1 - X - 4 * X ^ 2)) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (2 * X * (1 + X) * (1 - 2 * X) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      1 + (-((1 - Real.sqrt 17) / 2) ^ n + ((1 + Real.sqrt 17) / 2) ^ n) / Real.sqrt 17 := by
  sorry

end OMA.S_oeis_a265987
