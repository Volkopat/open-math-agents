import OMAReductions.R_Erdos342_erdos_342_parts_i_R1

-- Reduction Erdos342.erdos_342.parts.i.R1.H2.R1 of step Erdos342.erdos_342.parts.i.R1.H2
-- Credit: @arindale

/-!
# Propagating a broad-arc exception: the two sides of the arc

The target asks that a broad-arc exception at `a i` recurs at some `a j` with
`a i < a j ≤ 512 * a i`.  The complement of `Icc (21/100) (76/100)` has two sides, and they
propagate by different mechanisms: below `21/100` a translate by `2` (whose phase increment is
`2t ∈ [0.8185, 0.81854]`) is already an exception, while above `76/100` the phase may land back
inside the arc and the missing-translate alternative is needed.  We split the statement into the
two sides.
-/

namespace OMA.R_Erdos342_erdos_342_parts_i_R1_H2_R1

open Erdos342

/-- Low side: an exception with phase below `21/100` propagates within a factor of `512`. -/
def H1 : Prop :=
  ∀ a : ℕ → ℕ, IsUlamSequence a → ∀ t : ℝ,
    t ∈ Set.Icc (40925/100000 : ℝ) (40927/100000) →
    ∀ i, a i ≠ 2 → Int.fract (t * a i) < 21/100 →
      ∃ j, a i < a j ∧ a j ≤ 512 * a i ∧ a j ≠ 2 ∧
        Int.fract (t * a j) ∉ Set.Icc (21/100 : ℝ) (76/100)

/-- High side: an exception with phase above `76/100` propagates within a factor of `512`. -/
def H2 : Prop :=
  ∀ a : ℕ → ℕ, IsUlamSequence a → ∀ t : ℝ,
    t ∈ Set.Icc (40925/100000 : ℝ) (40927/100000) →
    ∀ i, a i ≠ 2 → 76/100 < Int.fract (t * a i) →
      ∃ j, a i < a j ∧ a j ≤ 512 * a i ∧ a j ≠ 2 ∧
        Int.fract (t * a j) ∉ Set.Icc (21/100 : ℝ) (76/100)

theorem main : H1 → H2 → OMA.R_Erdos342_erdos_342_parts_i_R1.H2 := by
  intro h1 h2 a ha t ht i hi₂ hnot
  by_cases hlo : Int.fract (t * a i) < (21/100 : ℝ)
  · exact h1 a ha t ht i hi₂ hlo
  · have hge : (21/100 : ℝ) ≤ Int.fract (t * a i) := le_of_not_gt hlo
    have hgt : (76/100 : ℝ) < Int.fract (t * a i) := by
      by_contra hle
      exact hnot ⟨hge, le_of_not_gt hle⟩
    exact h2 a ha t ht i hi₂ hgt

end OMA.R_Erdos342_erdos_342_parts_i_R1_H2_R1
