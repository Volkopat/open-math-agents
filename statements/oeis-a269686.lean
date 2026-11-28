import Mathlib

/-!
# A269686: length-n 0..4 arrays with no repeated value differing from the previous repeated
value by plus or minus one modulo 4+1

Source: https://oeis.org/A269686 (R. H. Hardin; conjectures from Colin Barker, Jan 27 2019)

An array `x_1, ..., x_n` over `{0, ..., 4}` (here `Fin 5`) has a repeated value at position `i`
when `x_i = x_(i-1)`; the value of that repeat is `x_i`. Listing the repeats from left to right,
each repeat value must not differ from the value of the previous repeat by `+1` or `-1`
modulo `5`. Arithmetic in `Fin 5` is modulo `5`. This reading reproduces all 22 data terms of
the entry (5, 25, 125, 615, 2995, ...).

The offset is 1. The generating function `Sum_(n>=1) a(n) x^n` is written as
`X * mk (fun n => a (n+1))`, and the rational identity is stated after clearing the
denominator (constant coefficient 1). The closed form is stated over `ℝ` for `n >= 1`.
-/

namespace OMA.S_oeis_a269686

/-- The values of the repeats of a word, from left to right: one entry `x_i` for each
position `i` with `x_i = x_(i-1)`. -/
def repeats : List (Fin 5) → List (Fin 5)
  | a :: b :: t => if a = b then a :: repeats (b :: t) else repeats (b :: t)
  | _ => []

/-- `s` differs from `r` by plus or minus one modulo 5. -/
def Adjacent (r s : Fin 5) : Prop := s = r + 1 ∨ s = r - 1

instance : DecidableRel Adjacent := fun r s => by unfold Adjacent; infer_instance

/-- No repeated value differs from the previous repeated value by plus or minus one
modulo 5. -/
def Valid (l : List (Fin 5)) : Prop :=
  List.IsChain (fun r s => ¬ Adjacent r s) (repeats l)

instance : DecidablePred Valid := fun l => by unfold Valid; infer_instance

/-- A269686(n): the number of length-n arrays over `0..4` with no repeated value
differing from the previous repeated value by plus or minus one modulo 5. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin n → Fin 5 => Valid (List.ofFn f))).card

open PowerSeries

/-- Colin Barker's conjectures for A269686: the generating function is
`5*x*(1 - 3*x - 2*x^2) / ((1 - 4*x)*(1 - 4*x - 3*x^2))`, and for `n >= 1`,
`a(n) = (-5/42)*(7*4^n + (2-sqrt(7))^n*(-7+3*sqrt(7)) - (2+sqrt(7))^n*(7+3*sqrt(7)))`. -/
theorem main :
    ((1 - 4 * X) * (1 - 4 * X - 3 * X ^ 2) * (X * mk (fun n => (a (n + 1) : ℤ))) =
      (5 * X * (1 - 3 * X - 2 * X ^ 2) : PowerSeries ℤ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = (-5 / 42) * (7 * 4 ^ n + (2 - Real.sqrt 7) ^ n * (-7 + 3 * Real.sqrt 7) -
        (2 + Real.sqrt 7) ^ n * (7 + 3 * Real.sqrt 7)) := by
  sorry

end OMA.S_oeis_a269686
