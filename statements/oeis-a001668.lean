import Mathlib

/-!
# OEIS A001668 (self-avoiding walks on the honeycomb lattice): `n^{11/32}` asymptotics

Source: https://oeis.org/A001668
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of `n`-step self-avoiding walks on the hexagonal (honeycomb) lattice from a
fixed vertex. With `μ = √(2 + √2)` (A179260, Duminil-Copin–Smirnov), the entry records the
conjecture `a(n) ~ μ^n n^{11/32}`. The usual form (Nienhuis) carries an unspecified amplitude,
`a(n) ~ A μ^n n^{11/32}`, and that is what is stated (`A > 0` exists); with `A = 1` literally
the claim would be a different, unconjectured constant identity.

Lattice: the honeycomb lattice in brick-wall form on `ℤ × ℤ`: `(x, y)` is adjacent to
`(x ± 1, y)`, and to `(x, y + 1)` if `x + y` is even, `(x, y - 1)` if `x + y` is odd.
-/

namespace OMA.S_oeis_a001668

open Filter

/-- Adjacency of the honeycomb (brick-wall) lattice. -/
def HexAdj (p q : ℤ × ℤ) : Prop :=
  (q.2 = p.2 ∧ (q.1 = p.1 + 1 ∨ q.1 = p.1 - 1)) ∨
  (q.1 = p.1 ∧ ((Even (p.1 + p.2) ∧ q.2 = p.2 + 1) ∨ (Odd (p.1 + p.2) ∧ q.2 = p.2 - 1)))

/-- `n`-step self-avoiding walks from the origin. -/
def SAW (n : ℕ) : Set (Fin (n + 1) → ℤ × ℤ) :=
  {w | w 0 = (0, 0) ∧ Function.Injective w ∧ ∀ i : Fin n, HexAdj (w i.castSucc) (w i.succ)}

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (SAW n)

/-- Nienhuis' conjecture `a(n) ~ A μ^n n^{11/32}`. -/
theorem main :
    ∃ A : ℝ, 0 < A ∧
      Tendsto (fun n : ℕ => (a n : ℝ) /
        (Real.sqrt (2 + Real.sqrt 2) ^ n * (n : ℝ) ^ ((11 : ℝ) / 32))) atTop (nhds A) := by
  sorry

end OMA.S_oeis_a001668
