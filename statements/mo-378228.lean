import Mathlib

/-!
# Rational metric projections onto rational polytopes

Source: Claudio Gorodski, https://mathoverflow.net/questions/378228 (CC BY-SA 4.0).
Credit: @connoranderson. Fedor Petrov's answer uses the active vertices and their
orthogonal supporting hyperplane. We use the same geometric observation.

For any rational target and nonempty finite family of rational vertices, the
nearest point has rational coordinates and the squared distance is rational.
The variational inequality gives, for every feasible real point, the stronger
Pythagorean lower bound and hence uniqueness. Taking the target to be the origin
is the original question.
-/
namespace OMA.S_mo_378228
open Set
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def embed {n : ℕ} (q : Fin n → ℚ) : E n :=
  WithLp.toLp 2 (fun i => (q i : ℝ))
def poly {n k : ℕ} (V : Fin k → Fin n → ℚ) : Set (E n) :=
  convexHull ℝ (range fun i => embed (V i))

theorem main : ∀ (n k : ℕ), 0<k → ∀ (V : Fin k → Fin n → ℚ) (q : Fin n → ℚ),
    ∃ r : Fin n → ℚ, embed r ∈ poly V ∧
      ‖embed q - embed r‖^2 = ((∑ j, (q j - r j)^2 : ℚ) : ℝ) ∧
      ∀ x ∈ poly V, ‖embed q - embed r‖^2 + ‖x - embed r‖^2 ≤ ‖embed q - x‖^2 := by
  sorry
end OMA.S_mo_378228
