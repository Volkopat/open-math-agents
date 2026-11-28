import Mathlib

/-!
# Asymptotic distribution of the form of polyhedra

Source https://www.openproblemgarden.org/op/asymptotic_distribution_of_form_of_polyhedra

For a uniformly chosen combinatorial type with e edges and v vertices
the form parameter is v / (e + 2). It converges in distribution to the
point mass at one half. The centered form parameter rescaled by the square
root of e converges to a centered normal law of variance 1/32.
See Bridges, https://arxiv.org/abs/2609.22402, Theorem 1.1.
-/

namespace OMA.S_opg_asymptotic_distribution_of_form_of_polyhedra

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def HasStraightLineDrawing {v : ℕ} (G : SimpleGraph (Fin v)) : Prop :=
  ∃ p : Fin v ↪ Plane,
    (∀ u w z, G.Adj u w → p z ∈ segment ℝ (p u) (p w) → z = u ∨ z = w) ∧
    ∀ u w x y, G.Adj u w → G.Adj x y →
      ({u, w} : Set (Fin v)) ≠ {x, y} →
      segment ℝ (p u) (p w) ∩ segment ℝ (p x) (p y) ⊆
        p '' (({u, w} : Set (Fin v)) ∩ {x, y})

/-- The graph characterization of convex three-dimensional polyhedra. -/
def IsPolyhedralGraph {v : ℕ} (G : SimpleGraph (Fin v)) : Prop :=
  4 ≤ v ∧ HasStraightLineDrawing G ∧
    ∀ removed : Finset (Fin v), removed.card < 3 →
      (G.induce (removed : Set (Fin v))ᶜ).Connected

abbrev GraphsWithCounts (e v : ℕ) :=
  {G : SimpleGraph (Fin v) // G.edgeSet.ncard = e ∧ IsPolyhedralGraph G}

/-- Each isomorphism class is counted once. -/
noncomputable def polyhedraCount (e v : ℕ) : ℕ :=
  Nat.card (Quot (fun G H : GraphsWithCounts e v => Nonempty (G.val ≃g H.val)))

noncomputable def totalCount (e : ℕ) : ℕ :=
  ∑ v ∈ Finset.range (e + 1), polyhedraCount e v

noncomputable def uniformAverage (e : ℕ) (test : ℕ → ℝ) : ℝ :=
  (∑ v ∈ Finset.range (e + 1), (polyhedraCount e v : ℝ) * test v) / totalCount e

noncomputable def form (e v : ℕ) : ℝ :=
  (v : ℝ) / ((e : ℝ) + 2)

noncomputable def admissibleEdgeLimit : Filter ℕ :=
  atTop ⊓ 𝓟 {e | 0 < totalCount e}

theorem main :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun e => uniformAverage e (fun v => f (form e v)))
        admissibleEdgeLimit (𝓝 (f (1 / 2))) ∧
      Tendsto (fun e => uniformAverage e
          (fun v => f (Real.sqrt e * (form e v - 1 / 2))))
        admissibleEdgeLimit (𝓝 (∫ x, f x ∂(gaussianReal 0 ((1 : ℝ≥0) / 32)))) := by
  sorry

end OMA.S_opg_asymptotic_distribution_of_form_of_polyhedra
