import OMAStatements.S_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum
import Mathlib

-- Based on OpenAI, openai/math @3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
namespace OMA.R_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum_R1
open MeasureTheory OMA.S_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum

def H1 : Prop :=
  let X := UnitAddCircle × UnitAddCircle × UnitAddCircle
  let m : Measure UnitAddCircle := AddCircle.haarAddCircle
  let μ : Measure X := m.prod (m.prod m)
  ∀ a : ℕ → C(X, ℂ), ((∀ i x, star (a i x) = a i x) ∧ (∀ i, ∫ x, a i x ∂μ = 0) ∧ (∀ i x, ‖a i x‖ ≤ 1)) →
    ∃ (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (f : Lp ℂ 2 μ),
      Orthonormal ℂ (orbit T hT f) ∧ (Submodule.span ℂ (Set.range (orbit T hT f))).topologicalClosure ≤ L2zero μ ∧
      ∀ i, (ContinuousMap.toLp 2 μ ℂ (a i)) ∈ (Submodule.span ℂ (Set.range (orbit T hT f))).topologicalClosure

def H2 : Prop :=
  let X := UnitAddCircle × UnitAddCircle × UnitAddCircle
  let m : Measure UnitAddCircle := AddCircle.haarAddCircle
  let μ : Measure X := m.prod (m.prod m)
  ∃ a : ℕ → C(X, ℂ), ((∀ i x, star (a i x) = a i x) ∧ (∀ i, ∫ x, a i x ∂μ = 0) ∧ (∀ i x, ‖a i x‖ ≤ 1)) ∧
    ∀ K : Submodule ℂ (Lp ℂ 2 μ), IsClosed (K : Set (Lp ℂ 2 μ)) →
      (∀ i, (ContinuousMap.toLp 2 μ ℂ (a i)) ∈ K) → L2zero μ ≤ K

def H3 : Prop :=
  let X := UnitAddCircle × UnitAddCircle × UnitAddCircle
  let m : Measure UnitAddCircle := AddCircle.haarAddCircle
  let μ : Measure X := m.prod (m.prod m)
  ∀ (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (f : Lp ℂ 2 μ),
    Orthonormal ℂ (orbit T hT f) → (Submodule.span ℂ (Set.range (orbit T hT f))).topologicalClosure = L2zero μ → Ergodic T μ

theorem main : H1 → H2 → H3 → type_of% @OMA.S_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum.main := by
  intro stage tests erg
  obtain ⟨a, ha, ht⟩ := tests
  obtain ⟨T,hT,f,ho,hle,hi⟩ := stage a ha
  have eqs := le_antisymm hle (ht _ (Submodule.isClosed_topologicalClosure _) hi)
  exact ⟨_, inferInstance, StandardBorelSpace.prod, _, inferInstance, T, hT, erg T hT f ho eqs, f, ho, eqs⟩

end OMA.R_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum_R1
