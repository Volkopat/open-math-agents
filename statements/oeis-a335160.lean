import Mathlib

/-!
# A335160: a(n) = nim-product of 2^3 and 2^n.

Source: https://oeis.org/A335160
Credit: @cblly (agent: Claude Code, model claude-opus-5-5)

The entry has offset 0 and data `8, 12, 11, 13, 128, 192, 176, 208, 2048, 3072, 2816, 3328, …`.
Its Formula section records:

  Conjectures from Colin Barker, Jun 11 2020:
  G.f.: (8 + 12*x + 11*x^2 + 13*x^3) / ((1 - 2*x)*(1 + 2*x)*(1 + 4*x^2)).
  a(n) = 16*a(n-4) for n>3.

Both conjectures are formalized, as a conjunction.

Conventions.
- Nim-multiplication of natural numbers is Conway's recursive definition (as in OEIS A051775):
  `a ⊗ b` is the least natural number different from `(a' ⊗ b) ⊕ (a ⊗ b') ⊕ (a' ⊗ b')` for all
  `a' < a` and `b' < b`, where `⊕` is bitwise exclusive or (`^^^`). Mathlib no longer contains
  nimbers, so the definition is given here. It reproduces the listed terms (checked by computer).
- `a n = 8 ⊗ 2 ^ n`, with offset 0.
- The generating function `∑_{n ≥ 0} a(n) x^n` is stated as a formal power series over `ℤ`,
  multiplied out by its denominator.
-/

namespace OMA.S_oeis_a335160

open PowerSeries

/-- Nim-multiplication on `ℕ`: the least natural number not of the form
`(a' ⊗ b) ⊕ (a ⊗ b') ⊕ (a' ⊗ b')` with `a' < a` and `b' < b`. -/
noncomputable def nimMul (a b : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ a' < a, ∀ b' < b, m ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b'}
termination_by a + b

/-- `a n`, the nim-product of `2 ^ 3` and `2 ^ n` (offset 0). -/
noncomputable def a (n : ℕ) : ℕ :=
  nimMul (2 ^ 3) (2 ^ n)

/-- Colin Barker's conjectures: `a(n) = 16 a(n-4)` for `n > 3`, and the rational generating
function `(8 + 12x + 11x^2 + 13x^3) / ((1 - 2x)(1 + 2x)(1 + 4x^2))`. -/
theorem main :
    (∀ n : ℕ, 3 < n → a n = 16 * a (n - 4)) ∧
    ((1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * PowerSeries.mk (fun n => (a n : ℤ)) =
      (8 + 12 * X + 11 * X ^ 2 + 13 * X ^ 3 : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a335160
