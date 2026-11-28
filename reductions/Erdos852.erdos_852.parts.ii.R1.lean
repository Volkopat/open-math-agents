import FormalConjectures.ErdosProblems.«852»

-- Reduction Erdos852.erdos_852.parts.ii.R1 of Erdős Problem 852 — ii
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos852_erdos_852_parts_ii_R1

open Erdos852

open Filter

def H1 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, (n : ℝ) < x → ∀ H : ℕ, DistinctGapRun n H → (H : ℝ) ≤ C * Real.log x / Real.log (Real.log x)

def H2 : Prop := ∀ C ε : ℝ, 0 < C → 0 < ε → ∀ᶠ x : ℝ in atTop, C * Real.log x / Real.log (Real.log x) ≤ ε * Real.log x

theorem main : H1 → H2 → type_of% @Erdos852.erdos_852.parts.ii := by
  intro h1 h2
  obtain ⟨C, hC, h1x⟩ := h1
  intro ε hε
  have h2x := h2 C ε hC hε
  filter_upwards [h1x, h2x] with x hx1 hx2
  intro n hn H hr
  exact le_trans (hx1 n hn H hr) hx2

end OMA.R_Erdos852_erdos_852_parts_ii_R1
