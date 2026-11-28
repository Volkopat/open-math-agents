import Mathlib

/-!
# OEIS A401548: Asymptotic for optimal greedy sums of positive squares

Source: https://oeis.org/A401548

For a positive integer, repeatedly subtract its largest square until it reaches
zero. Call the initial integer optimal if the number of subtractions is the
least length of a sum of positive squares representing it. Abo Khmiss
conjectures a positive constant times `N^(15/16)` for the number of optimal
integers through `N`.
-/

namespace OMA.S_oeis_a401548

open Filter Topology

/-- Number of subtractions by the greedy algorithm. -/
def greedyLength : (n : ℕ) → ℕ
  | 0 => 0
  | n + 1 => 1 + greedyLength (n + 1 - (n + 1).sqrt ^ 2)
termination_by n => n
decreasing_by
  have hs : 0 < (n + 1).sqrt := Nat.sqrt_pos.mpr (by omega)
  have hsq : 0 < ((n + 1).sqrt) ^ 2 := pow_pos hs 2
  omega

/-- A sum of exactly `k` positive squares. -/
def Represents (n k : ℕ) : Prop :=
  ∃ a : Fin k → ℕ, (∀ i, 0 < a i) ∧ (∑ i, (a i) ^ 2) = n

/-- Number of optimal positive inputs through `N`. -/
noncomputable def optimalCount (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter (fun n =>
    Represents n (greedyLength n) ∧ ∀ k < greedyLength n, ¬ Represents n k)).card

/-- The conjectured asymptotic with an unspecified positive coefficient. -/
theorem main :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun N : ℕ => (optimalCount N : ℝ) / (N : ℝ) ^ (15 / 16 : ℝ))
        atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a401548
