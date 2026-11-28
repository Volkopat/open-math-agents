import Mathlib

/-!
# Post-composition of an integral with a diffeomorphism

Source: https://mathoverflow.net/questions/220167
Asked by MathOverflow user AB_IM.

Let `(Ω, 𝔉, μ)` be a measure space, `f : Ω → E` a weakly measurable function to a Banach
space `E` (for simplicity reflexive) and `g : E → E'` a diffeomorphism. Question 1 asks:
is it true that `g (∫_Ω f dμ) = ∫_Ω g ∘ f dμ`, the integrals being Pettis integrals?
(Question 2 asks for which `g` this holds; it is not formalized here.)

Translation choices.
* The spaces `E` and `E'` are taken finite dimensional real normed spaces (in particular
  reflexive Banach spaces). For them weak and strong measurability agree and the Pettis
  integral of an integrable function is its Bochner integral, written `∫ ω, f ω ∂μ`. To
  make sure that both integrals in the identity exist, `f` and `g ∘ f` are assumed
  integrable.
* A diffeomorphism is a bijection `g` that is `C^∞` with a `C^∞` inverse `h`.
* `main` is the affirmative answer to Question 1 for all such data.
-/

namespace OMA.S_mo_220167

open MeasureTheory

theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
      (g : E → E'), ContDiff ℝ (⊤ : ℕ∞) g →
      (∃ h : E' → E, ContDiff ℝ (⊤ : ℕ∞) h ∧ Function.LeftInverse h g ∧
        Function.RightInverse h g) →
      ∀ f : Ω → E, Integrable f μ → Integrable (fun ω => g (f ω)) μ →
        g (∫ ω, f ω ∂μ) = ∫ ω, g (f ω) ∂μ := by
  sorry

end OMA.S_mo_220167
