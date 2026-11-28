import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Resolving the two-envelope switching question

Source: MathOverflow 253088; mathematical explanation by usul (26 October 2016).
The sample space is a finite prior index together with an independent fair coin.
Conditional quantities are normalized sums over the actual observation event.
-/

namespace OMA.S_mo_253088

open Finset

variable {ι : Type*} [Fintype ι]

/-- `true` selects the smaller envelope. -/
def opened (a : ι → ℝ) (ω : ι × Bool) : ℝ :=
  if ω.2 then a ω.1 else 2 * a ω.1

def other (a : ι → ℝ) (ω : ι × Bool) : ℝ :=
  if ω.2 then 2 * a ω.1 else a ω.1

/-- Joint probability mass of the prior and an independent fair coin. -/
noncomputable def mass (w : ι → ℝ) (ω : ι × Bool) : ℝ := w ω.1 / 2

noncomputable def expectation (w : ι → ℝ) (f : ι × Bool → ℝ) : ℝ :=
  ∑ ω, mass w ω * f ω

noncomputable def observationMass (w a : ι → ℝ) (v : ℝ) : ℝ := by
  classical
  exact ∑ ω, if opened a ω = v then mass w ω else 0

noncomputable def smallerMass (w a : ι → ℝ) (v : ℝ) : ℝ := by
  classical
  exact ∑ ω, if opened a ω = v ∧ ω.2 = true then mass w ω else 0

noncomputable def posterior (w a : ι → ℝ) (v : ℝ) : ℝ :=
  smallerMass w a v / observationMass w a v

noncomputable def conditionalOther (w a : ι → ℝ) (v : ℝ) : ℝ := by
  classical
  exact (∑ ω, if opened a ω = v then mass w ω * other a ω else 0) /
    observationMass w a v

theorem main :
    (∀ (n : ℕ) (w a : Fin n → ℝ), (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
      (∀ i, 0 < a i) →
      (∀ ω, 0 ≤ mass w ω) ∧ (∑ ω, mass w ω) = 1 ∧
      expectation w (opened a) = expectation w (other a) ∧
      ∀ v : ℝ, 0 < v → 0 < observationMass w a v →
        (0 ≤ posterior w a v ∧ posterior w a v ≤ 1) ∧
        conditionalOther w a v - v = v * (3 * posterior w a v - 1) / 2 ∧
        (v < conditionalOther w a v ↔ (1 / 3 : ℝ) < posterior w a v)) ∧
    (let w : Unit → ℝ := fun _ => 1
     let a : Unit → ℝ := fun _ => 2
     let b : Unit → ℝ := fun _ => 1
     (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
     (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧
     observationMass w a 2 = 1 / 2 ∧ observationMass w b 2 = 1 / 2 ∧
     posterior w a 2 = 1 ∧ posterior w b 2 = 0 ∧
     conditionalOther w a 2 = 4 ∧ conditionalOther w b 2 = 1) := by
  sorry

end OMA.S_mo_253088
