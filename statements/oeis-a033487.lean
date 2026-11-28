import Mathlib

/-!
# Crossing numbers of cocktail party graphs

Eric Weisstein's April 29, 2019 conjecture in OEIS A033487 concerns ordinary planar drawings
with curved edges. Each of the `k` parts has two vertices. The ordering of the part indices
gives every undirected edge one orientation. The source indexes the sequence from `n = 0`,
which corresponds to the octahedral graph (`k = 3`).

Source: https://oeis.org/A033487. The local-chart description of a crossing follows
OpenAI's ComparatorChallenges/CompleteCrossing.lean, commit 3344da59991ed94f9ba711217b29c1d760badfa6
(Apache-2.0), also used in this project's Hill-conjecture statement.

Credit: @connoranderson
-/

namespace OMA.S_oeis_a033487

abbrev Plane := ℝ × ℝ
abbrev Vertex (k : ℕ) := Fin k × Bool
abbrev Edge (k : ℕ) := {e : Vertex k × Vertex k // e.1.1 < e.2.1}

structure Drawing (k : ℕ) where
  pos : Vertex k → Plane
  pos_injective : Function.Injective pos
  arc (e : Edge k) : Path (pos e.val.1) (pos e.val.2)
  arc_injective (e : Edge k) : Function.Injective (arc e)
  avoids_vertices (e : Edge k) (t : unitInterval) : t ∈ Set.Ioo 0 1 →
    ∀ v : Vertex k, arc e t ≠ pos v

def arcInterior {k : ℕ} (D : Drawing k) (e : Edge k) : Set Plane :=
  D.arc e '' Set.Ioo (0 : unitInterval) 1

def crossingPoints {k : ℕ} (D : Drawing k) : Set Plane :=
  {p | ∃ e f : Edge k, e ≠ f ∧ p ∈ arcInterior D e ∧ p ∈ arcInterior D f}

/-- The two arcs cross if in suitable local coordinates they are the two coordinate axes. -/
def crossesAt (A B : Set Plane) (p : Plane) : Prop :=
  ∃ chart : OpenPartialHomeomorph Plane Plane, p ∈ chart.source ∧ chart p = (0, 0) ∧
    chart '' (chart.source ∩ A) = chart.target ∩ {z | z.2 = 0} ∧
    chart '' (chart.source ∩ B) = chart.target ∩ {z | z.1 = 0}

def Admissible {k : ℕ} (D : Drawing k) : Prop :=
  (crossingPoints D).Finite ∧
  (∀ e f : Edge k, e ≠ f → ∀ p ∈ arcInterior D e ∩ arcInterior D f,
    crossesAt (arcInterior D e) (arcInterior D f) p) ∧
  (∀ e f g : Edge k, e ≠ f → f ≠ g → e ≠ g →
    arcInterior D e ∩ arcInterior D f ∩ arcInterior D g = ∅)

/-- The attainable crossing counts among finite, proper drawings in general position. -/
def crossingCounts (k : ℕ) : Set ℕ :=
  {c | ∃ D : Drawing k, Admissible D ∧ (crossingPoints D).ncard = c}

theorem main : ∀ n : ℕ,
    IsLeast (crossingCounts (n + 3)) (n * (n + 1) * (n + 2) * (n + 3) / 4) := by
  sorry

end OMA.S_oeis_a033487
