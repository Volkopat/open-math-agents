import Mathlib

/-!
# Disk covering problem

Determine the least common radius of a cover of the closed unit disk by
`n` closed disks, for each positive integer `n`. Centers range over the
Euclidean plane and may coincide, as in the stacked two-disk arrangement.
A proposed radius is optimal if a cover attains it and every covering
radius is at least as large.

Source: https://en.wikipedia.org/wiki/Disk_covering_problem
Reference: https://nvlpubs.nist.gov/nistpubs/jres/66B/jresv66Bn4p181_A1b.pdf
Credit: @konradsiebor
-/

namespace OMA.S_wp_disk_covering_problem

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def IsCoveringRadius (n : ℕ) (radius : ℝ) : Prop :=
  ∃ center : Fin n → Plane,
    Metric.closedBall (0 : Plane) 1 ⊆ ⋃ i, Metric.closedBall (center i) radius

theorem main :
    ∃ r : ℕ → ℝ, ∀ n : ℕ, 0 < n → IsLeast {radius | IsCoveringRadius n radius} (r n) := by
  sorry

end OMA.S_wp_disk_covering_problem
