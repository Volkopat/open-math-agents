import Mathlib

/-!
# A335161: a(n) = nim-product of 2^4 and 2^n.

Source: https://oeis.org/A335161
Credit: @cblly (agent: Claude Code, model claude-opus-5-5)

The entry has offset 0 and data `16, 32, 64, 128, 24, 44, 75, 141, 4096, 8192, 16384, 32768, …`.
Its Formula section records:

  Conjectures from Colin Barker, Jun 11 2020:
  G.f.: (16 + 32*x + 64*x^2 + 128*x^3 + 24*x^4 + 44*x^5 + 75*x^6 + 141*x^7) /
    ((1 - 2*x)*(1 + 2*x)*(1 + 4*x^2)*(1 + 16*x^4)).
  a(n) = 256*a(n-8) for n>7.

Both conjectures are formalized, as a conjunction.

Conventions.
- Nim-multiplication of natural numbers is Conway's recursive definition (as in OEIS A051775):
  `a ⊗ b` is the least natural number different from `(a' ⊗ b) ⊕ (a ⊗ b') ⊕ (a' ⊗ b')` for all
  `a' < a` and `b' < b`, where `⊕` is bitwise exclusive or (`^^^`). Mathlib no longer contains
  nimbers, so the definition is given here. It reproduces the listed terms (checked by computer).
- `a n = 16 ⊗ 2 ^ n`, with offset 0.
- The generating function `∑_{n ≥ 0} a(n) x^n` is stated as a formal power series over `ℤ`,
  multiplied out by its denominator.
-/

namespace OMA.S_oeis_a335161

open PowerSeries

/-- Nim-multiplication on `ℕ`: the least natural number not of the form
`(a' ⊗ b) ⊕ (a ⊗ b') ⊕ (a' ⊗ b')` with `a' < a` and `b' < b`. -/
noncomputable def nimMul (a b : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ a' < a, ∀ b' < b, m ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b'}
termination_by a + b

/-- `a n`, the nim-product of `2 ^ 4` and `2 ^ n` (offset 0). -/
noncomputable def a (n : ℕ) : ℕ :=
  nimMul (2 ^ 4) (2 ^ n)

/-- Colin Barker's conjectures: `a(n) = 256 a(n-8)` for `n > 7`, and the rational generating
function `(16 + 32x + 64x^2 + 128x^3 + 24x^4 + 44x^5 + 75x^6 + 141x^7) /
((1 - 2x)(1 + 2x)(1 + 4x^2)(1 + 16x^4))`. -/
theorem main :
    (∀ n : ℕ, 7 < n → a n = 256 * a (n - 8)) ∧
    ((1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * (1 + 16 * X ^ 4) *
        PowerSeries.mk (fun n => (a n : ℤ)) =
      (16 + 32 * X + 64 * X ^ 2 + 128 * X ^ 3 + 24 * X ^ 4 + 44 * X ^ 5 + 75 * X ^ 6 + 141 * X ^ 7 :
        PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a335161
