import Mathlib

/-!
# OEIS A035313: diagonal of the Zorach additive triangle

Source: https://oeis.org/A035313
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The Zorach additive triangle (A035312) has rows `T(n, 0), …, T(n, n)`, `T(0, 0) = 1`. Each entry
is the sum of its west and northwest neighbours, `T(n, k) = T(n, k-1) + T(n-1, k-1)`, and
`T(n, 0)` is the least positive integer such that row `n` repeats no number of the table so far
(neither within the row nor from earlier rows). `a(n) = T(n, n)` is A035313.

Conjectures (D. W. Wilson, 2012, OEIS entry):
* every positive integer occurs in the sequence or in one of its `j`-th differences;
* `a(n+1)/a(n) → 2`.

Conventions:
* The `j`-th difference sequence is the iterated forward difference
  `Δa(n) = a(n+1) - a(n)`, computed in `ℤ`; the `0`-th difference is `a` itself.
* `main` states both conjectures.
-/

namespace OMA.S_oeis_a035313

open Filter Topology

/-- The row with first entry `m` following the row `prev`: `[m, m + p₀, m + p₀ + p₁, …]`. -/
def nextRow (prev : List ℕ) (m : ℕ) : List ℕ :=
  prev.scanl (· + ·) m

/-- `m` is an admissible first entry for the row after `prev`, given the numbers `used`. -/
def Admissible (used prev : List ℕ) (m : ℕ) : Prop :=
  0 < m ∧ (nextRow prev m).Nodup ∧ ∀ x ∈ nextRow prev m, x ∉ used

/-- After row `n`: (all numbers used so far, row `n`). -/
noncomputable def state : ℕ → List ℕ × List ℕ
  | 0 => ([1], [1])
  | n + 1 =>
    let s := state n
    let r := nextRow s.2 (sInf {m | Admissible s.1 s.2 m})
    (s.1 ++ r, r)

/-- A035313: `a(n) = T(n, n)`, the last entry of row `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  (state n).2.getLastD 0

/-- The `j`-th forward difference of an integer sequence. -/
def diff : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, f => f
  | j + 1, f => fun n => diff j f (n + 1) - diff j f n

/-- Wilson's two conjectures on A035313. -/
theorem main :
    (∀ m : ℕ, 0 < m → ∃ j n : ℕ, diff j (fun k => (a k : ℤ)) n = m) ∧
    Tendsto (fun n => (a (n + 1) : ℝ) / a n) atTop (𝓝 2) := by
  sorry

end OMA.S_oeis_a035313
