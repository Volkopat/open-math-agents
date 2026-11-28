import Mathlib

/-!
# A007980: Expansion of (1 + x^2) / ((1 - x)^2 * (1 - x^3))

Source: https://oeis.org/A007980
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Zakharov's conjecture, proved):
`a(n)`, the `n`-th coefficient of `(1 + x^2) / ((1 - x)^2 * (1 - x^3))`, is the
maximum number of pieces (connected components) into which an open triangle can be
cut by `n` cevians (open line segments connecting a vertex to an interior point of
the opposite side).
-/

namespace OMA.S_oeis_a007980

/-- Coefficient of `x^n` in `(1 + x^2) / ((1 - x)^2 * (1 - x^3))`, satisfying
`(1 - 2x + x^2 - x^3 + 2x^4 - x^5) * A(x) = 1 + x^2`. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 7
  | 4 => 10
  | n + 5 => 2 * a (n + 4) - a (n + 3) + a (n + 2) - 2 * a (n + 1) + a n

/-- The standard open triangle with vertices `(0, 0)`, `(1, 0)`, and `(0, 1)`. -/
def openTriangle : Set (ℝ × ℝ) :=
  { p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1 }

/-- The `v`-th vertex of the standard triangle. -/
def vertex : Fin 3 → ℝ × ℝ
  | ⟨0, _⟩ => (0, 0)
  | ⟨1, _⟩ => (1, 0)
  | ⟨2, _⟩ => (0, 1)

/-- The point at parameter `t ∈ (0, 1)` on the side opposite to vertex `v`. -/
def oppositePoint (v : Fin 3) (t : ℝ) : ℝ × ℝ :=
  match v with
  | ⟨0, _⟩ => (1 - t, t)
  | ⟨1, _⟩ => (0, t)
  | ⟨2, _⟩ => (t, 0)

/-- The open cevian from vertex `v` to `oppositePoint v t`. -/
def cevianSet (v : Fin 3) (t : ℝ) : Set (ℝ × ℝ) :=
  { p | ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      p = ((1 - s) * (vertex v).1 + s * (oppositePoint v t).1,
           (1 - s) * (vertex v).2 + s * (oppositePoint v t).2) }

/-- For every `n : ℕ`, the maximum number of connected components of `openTriangle`
minus `n` cevians equals `a(n)`. -/
theorem main :
    ∀ n : ℕ,
      IsGreatest
        { m : ℕ | ∃ c : Fin n → Fin 3 × ℝ,
            (∀ i, 0 < (c i).2 ∧ (c i).2 < 1) ∧
            m = Nat.card (ConnectedComponents ↑(openTriangle \ ⋃ i, cevianSet (c i).1 (c i).2)) }
        (a n).toNat := by
  sorry

end OMA.S_oeis_a007980
