import Mathlib

/-!
# A269689: length-n 0..7 arrays with no repeated value differing from the previous repeated
value by plus or minus one modulo 7+1

Source: https://oeis.org/A269689 (R. H. Hardin; conjectures from Colin Barker, Jan 27 2019)

An array `x_1, ..., x_n` over `{0, ..., 7}` (here `Fin 8`) has a repeated value at position `i`
when `x_i = x_(i-1)`; the value of that repeat is `x_i`. Listing the repeats from left to right,
each repeat value must not differ from the value of the previous repeat by `+1` or `-1`
modulo `8`. Arithmetic in `Fin 8` is modulo `8`. This reading reproduces all 19 data terms of
the entry (8, 64, 512, 4080, 32416, ...).

The offset is 1. The generating function `Sum_(n>=1) a(n) x^n` is written as
`X * mk (fun n => a (n+1))`, and the rational identity is stated after clearing the
denominator (constant coefficient 1). The closed form is stated over `ℝ` for `n >= 1`;
its factor `2^(1-n)` is an integer power `(2 : ℝ) ^ ((1 : ℤ) - n)`.
-/

namespace OMA.S_oeis_a269689

/-- The values of the repeats of a word, from left to right: one entry `x_i` for each
position `i` with `x_i = x_(i-1)`. -/
def repeats : List (Fin 8) → List (Fin 8)
  | a :: b :: t => if a = b then a :: repeats (b :: t) else repeats (b :: t)
  | _ => []

/-- `s` differs from `r` by plus or minus one modulo 8. -/
def Adjacent (r s : Fin 8) : Prop := s = r + 1 ∨ s = r - 1

instance : DecidableRel Adjacent := fun r s => by unfold Adjacent; infer_instance

/-- No repeated value differs from the previous repeated value by plus or minus one
modulo 8. -/
def Valid (l : List (Fin 8)) : Prop :=
  List.IsChain (fun r s => ¬ Adjacent r s) (repeats l)

instance : DecidablePred Valid := fun l => by unfold Valid; infer_instance

/-- A269689(n): the number of length-n arrays over `0..7` with no repeated value
differing from the previous repeated value by plus or minus one modulo 8. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin n → Fin 8 => Valid (List.ofFn f))).card

open PowerSeries

/-- Colin Barker's conjectures for A269689: the generating function is
`8*x*(1 - 6*x - 5*x^2) / ((1 - 7*x)*(1 - 7*x - 6*x^2))`, and for `n >= 1`,
`a(n) = (2^(1-n)*(-73*2^(2+n)*7^n - 7*(7-sqrt(73))^n*(-73+9*sqrt(73))
  + 7*(7+sqrt(73))^n*(73+9*sqrt(73)))) / 1533`. -/
theorem main :
    ((1 - 7 * X) * (1 - 7 * X - 6 * X ^ 2) * (X * mk (fun n => (a (n + 1) : ℤ))) =
      (8 * X * (1 - 6 * X - 5 * X ^ 2) : PowerSeries ℤ)) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = ((2 : ℝ) ^ ((1 : ℤ) - n) * (-73 * 2 ^ (2 + n) * 7 ^ n -
        7 * (7 - Real.sqrt 73) ^ n * (-73 + 9 * Real.sqrt 73) +
        7 * (7 + Real.sqrt 73) ^ n * (73 + 9 * Real.sqrt 73))) / 1533 := by
  sorry

end OMA.S_oeis_a269689
