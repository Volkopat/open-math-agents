import FormalConjectures.Paper.RiemannHypothesisEquivalents

-- Reduction RiemannHypothesis.weil_positivity_criterion_rhs.R1 of RiemannHypothesis
-- Credit: @kyka776
/-!
The Guinand–Weil explicit formula expresses the sum of local Weil terms as a sum over
the nontrivial zeros, counted with multiplicity. For a test function convolved with its
reflection, the two pole terms vanish. A zero on the critical line pairs a transform
value with its complex conjugate, making the negative of the zero sum nonpositive.
-/

namespace OMA.R_RiemannHypothesis_weil_positivity_criterion_rhs_R1

open MeasureTheory RiemannHypothesis
open scoped CompactlySupported ComplexConjugate ContDiff Convolution

def H1 : Prop := RiemannHypothesis

/-- The explicit formula for real smooth test functions in the upstream normalization.
The two factors in the zero term are the transforms of a function and its reflection. -/
def H2 : Prop :=
  ∀ (g : C_c(ℝ, ℝ)), ContDiff ℝ ∞ g → IsTestFunction g →
    let F (z : ℂ) := ∫ x : ℝ, (g x : ℂ) * Complex.exp ((z - (1 / 2 : ℝ)) * (x : ℂ))
    weilArchimedean (g ⋆ fun x ↦ g (-x)) +
      ∑' p : Nat.Primes, weilNonArchimedean p (g ⋆ fun x ↦ g (-x)) =
      -(∑' z : {s : ℂ // 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0},
        (analyticOrderNatAt riemannZeta (z : ℂ) : ℝ) * (F z * F (1 - (z : ℂ))).re)

lemma transform_reflection (g : ℝ → ℝ) {z : ℂ} (hz : z.re = 1 / 2) :
    (∫ x : ℝ, (g x : ℂ) * Complex.exp (((1 - z) - (1 / 2 : ℝ)) * (x : ℂ))) =
      conj (∫ x : ℝ, (g x : ℂ) * Complex.exp ((z - (1 / 2 : ℝ)) * (x : ℂ))) := by
  have hshift : (1 - z) - (1 / 2 : ℝ) = conj (z - (1 / 2 : ℝ)) := by
    apply Complex.ext
    · norm_num [Complex.sub_re, hz]
    · simp
  rw [hshift, ← integral_conj]
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]

theorem main : H1 → H2 → type_of% @RiemannHypothesis.weil_positivity_criterion_rhs := by
  intro hRH hExplicit g hg ht
  rw [hExplicit g hg ht]
  apply neg_nonpos.mpr
  apply tsum_nonneg
  intro z
  have hntrivial : ¬ ∃ n : ℕ, (z : ℂ) = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have he := congrArg Complex.re hn
    norm_num [Complex.mul_re] at he
    linarith [z.property.1, Nat.cast_nonneg (α := ℝ) n]
  have hnpole : (z : ℂ) ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith [z.property.2.1]
  have hz := hRH z z.property.2.2 hntrivial hnpole
  apply mul_nonneg (Nat.cast_nonneg _)
  dsimp only
  rw [transform_reflection g hz, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end OMA.R_RiemannHypothesis_weil_positivity_criterion_rhs_R1
