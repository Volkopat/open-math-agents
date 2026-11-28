import Mathlib

/-!
# OEIS A137432: kings on a cylindrical chessboard

Source: https://oeis.org/A137432
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of ways to place `n²` nonattacking kings on a `2n × 2n` cylindrical
chessboard. Conjecture (OEIS entry): `lim_{n → ∞} a(n+1) / (n a(n)) = e`.

Conventions:
* The board is `Fin (2n) × ZMod (2n)`: rows `Fin (2n)` (not wrapped), columns `ZMod (2n)`
  (wrapped). Two distinct squares attack each other (king move) if their rows differ by at most
  `1` and their columns differ by `0` or `±1` in `ZMod (2n)`. A placement is a set of `n²`
  pairwise non-attacking squares. `n ≥ 1`.
-/

namespace OMA.S_oeis_a137432

open Filter Topology

/-- Two squares are a king move apart on the cylinder (columns wrap). -/
def Attacks (n : ℕ) (p q : Fin (2 * n) × ZMod (2 * n)) : Prop :=
  p ≠ q ∧ ((p.1 : ℕ) ≤ (q.1 : ℕ) + 1 ∧ (q.1 : ℕ) ≤ (p.1 : ℕ) + 1) ∧
    (p.2 = q.2 ∨ p.2 = q.2 + 1 ∨ q.2 = p.2 + 1)

/-- Number of placements of `n²` nonattacking kings. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {S : Finset (Fin (2 * n) × ZMod (2 * n)) //
    S.card = n ^ 2 ∧ ∀ p ∈ S, ∀ q ∈ S, ¬ Attacks n p q}

/-- `a(n+1) / (n a(n)) → e`. -/
theorem main :
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (n * a n)) atTop (𝓝 (Real.exp 1)) := by
  sorry

end OMA.S_oeis_a137432
