import Mathlib

/-!
# OEIS A208079: Barker's generating function and closed form

Source: https://oeis.org/A208079 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of 4 X n 0..1 arrays avoiding 0 0 0 and 0 0 1
horizontally and 0 0 0 and 0 1 0 vertically. Data: 9, 81, 441, 2601, 15129, 88209, ...
Formula section: Conjectures from Colin Barker, Jan 20 2018:
G.f.: 9*x*(1 + 4*x - x^2) / ((1 + x)*(1 - 6*x + x^2)).
a(n) = (9/4)*(2*(-1)^n + (3-2*sqrt(2))^n + (3+2*sqrt(2))^n).

Formalization notes:
* An array is a function `A : Fin 4 → Fin n → Fin 2` (row, then column). Row `i` read from
  left to right is `List.ofFn (A i)`, column `j` read from top to bottom is
  `List.ofFn fun i => A i j`.
* Avoiding a pattern horizontally means that no row contains it as a block of consecutive
  entries (`List.IsInfix`, written `<:+:`); vertically, the same for every column.
  This reading reproduces all 20 data terms of the entry.
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a208079

open PowerSeries

/-- A `4 × n` binary array is valid when no row contains `0 0 0` or `0 0 1` as consecutive
entries and no column contains `0 0 0` or `0 1 0` as consecutive entries. -/
def valid (n : ℕ) (A : Fin 4 → Fin n → Fin 2) : Prop :=
  (∀ i : Fin 4, ¬ [0, 0, 0] <:+: List.ofFn (A i) ∧ ¬ [0, 0, 1] <:+: List.ofFn (A i)) ∧
  (∀ j : Fin n, ¬ [0, 0, 0] <:+: List.ofFn (fun i => A i j) ∧
    ¬ [0, 1, 0] <:+: List.ofFn (fun i => A i j))

instance (n : ℕ) : DecidablePred (valid n) := fun A => by
  unfold valid; infer_instance

/-- A208079(n): the number of `4 × n` binary arrays avoiding `0 0 0` and `0 0 1` horizontally
and `0 0 0` and `0 1 0` vertically. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (valid n)).card

/-- Barker's conjectures for A208079 (offset 1): the generating function
9x(1 + 4x - x^2) / ((1 + x)(1 - 6x + x^2)), and the closed form for n >= 1. -/
theorem main :
    (1 + X) * (1 - 6 * X + X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (9 * X * (1 + 4 * X - X ^ 2) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      9 / 4 * (2 * (-1) ^ n + (3 - 2 * Real.sqrt 2) ^ n + (3 + 2 * Real.sqrt 2) ^ n) := by
  sorry

end OMA.S_oeis_a208079
