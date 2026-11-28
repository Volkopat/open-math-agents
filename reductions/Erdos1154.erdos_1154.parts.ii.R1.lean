import FormalConjectures.ErdosProblems.«1154»

/-!
# Erdős problem 1154 (ii): fields of every Hausdorff dimension in [0,1]

The pinned module already proves the two endpoint witnesses: `⊥` (the rationals) has
Hausdorff dimension 0, and `⊤` (the reals) has Hausdorff dimension 1. The genuinely open
part is the whole interior `0 < a < 1`. This reduction separates those proved endpoint
witnesses from the open interior; `main` uses both hypotheses, since the endpoints of
`Icc` are demanded by the target.
-/

-- Reduction Erdos1154.erdos_1154.parts.ii.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos1154_erdos_1154_parts_ii_R1

open scoped ENNReal Cardinal
open Set MeasureTheory

/-- Proved bridge: both endpoints of `Icc 0 1` are realised by subfields of `ℝ`. -/
def H1 : Prop :=
  (∃ R : Subfield ℝ, dimH (R : Set ℝ) = 0) ∧
  (∃ R : Subfield ℝ, dimH (R : Set ℝ) = 1)

/-- Open core: every strictly interior dimension is realised by a subfield of `ℝ`. -/
def H2 : Prop :=
  ∀ a ∈ Set.Ioo (0 : ℝ≥0∞) 1, ∃ R : Subfield ℝ, dimH (R : Set ℝ) = a

theorem main : H1 → H2 → type_of% @Erdos1154.erdos_1154.parts.ii := by
  intro h1 h2 a ha
  rcases h1 with ⟨hz, ho⟩
  rcases ha with ⟨ha0, ha1⟩
  rcases eq_or_lt_of_le ha0 with h | ha0lt
  · subst a
    exact hz
  · rcases eq_or_lt_of_le ha1 with h | halt
    · subst a
      exact ho
    · exact h2 a ⟨ha0lt, halt⟩

end OMA.R_Erdos1154_erdos_1154_parts_ii_R1
