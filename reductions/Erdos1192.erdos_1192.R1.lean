import FormalConjectures.ErdosProblems.«1192»

-- Reduction Erdos1192.erdos_1192.R1 of Erdős Problem 1192
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: split by the order r of the basis. Different r are unrelated (a basis of order 2 with
-- a small second moment says nothing about order 3, and conversely), so the split is genuine.
--   H1: r = 2. Known: Ruzsa (1990); stated exactly as upstream variants.ruzsa.
--   H2: every r ≥ 3. This is the open part.
-- main: case split on r = 2 or r ≥ 3. No computer search was used.

namespace OMA.R_Erdos1192_erdos_1192_R1

open Erdos1192 Filter Finset

def H1 : Prop :=
  ∃ A : Set ℕ,
    (∀ᶠ n in atTop, f_r A 2 n > 0) ∧
    (fun (x : ℕ) ↦ ∑ n ∈ range (x + 1), (f_r A 2 n : ℝ) ^ 2) =O[atTop]
      (fun (x : ℕ) ↦ (x : ℝ))

def H2 : Prop :=
  ∀ r ≥ 3, ∃ A : Set ℕ,
    (∀ᶠ n in atTop, f_r A r n > 0) ∧
    (fun (x : ℕ) ↦ ∑ n ∈ range (x + 1), (f_r A r n : ℝ) ^ 2) =O[atTop]
      (fun (x : ℕ) ↦ (x : ℝ))

theorem main : H1 → H2 → type_of% @Erdos1192.erdos_1192 := by
  intro h1 h2 r hr
  rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | h
  · simpa [H1] using h1
  · exact h2 r h

end OMA.R_Erdos1192_erdos_1192_R1
