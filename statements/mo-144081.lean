import Mathlib

/-!
# Gilbert–Pollak conjecture on the Steiner ratio

Source: https://mathoverflow.net/questions/144081
For a finite set `P` of points in the plane, let `L_s(P)` be the length of a Steiner minimum
tree and `L_m(P)` the length of a minimum spanning tree. Gilbert and Pollak conjectured that
the Steiner ratio `inf L_s(P)/L_m(P)` is `√3/2`. The equilateral triangle attains `√3/2`, so
the conjecture is the inequality `L_s(P) ≥ (√3/2) L_m(P)` for all `P` (Du and Hwang's 1990
proof has been disputed, as the question explains).

Conventions. `mstLength Q` is the minimum total Euclidean length of a connected simple graph
on the finite point set `Q` (a minimum spanning tree). `L_s(P)` is the infimum of
`mstLength (P ∪ S)` over finite sets `S` of Steiner points.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_144081

/-- Minimum total length of a connected simple graph on the point set `Q`. -/
noncomputable def mstLength (Q : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sInf {L | ∃ G : SimpleGraph Q, ∃ _ : DecidableRel G.Adj, G.Connected ∧
    L = ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun (x y : Q) => dist (x : EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 2)),
      fun x y => dist_comm _ _⟩ e}

/-- Length of a Steiner minimum tree of `P`. -/
noncomputable def steinerLength (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sInf {L | ∃ S : Finset (EuclideanSpace ℝ (Fin 2)), L = mstLength (P ∪ S)}

theorem main :
    ∀ P : Finset (EuclideanSpace ℝ (Fin 2)), 2 ≤ P.card →
      Real.sqrt 3 / 2 * mstLength P ≤ steinerLength P := by
  sorry

end OMA.S_mo_144081
