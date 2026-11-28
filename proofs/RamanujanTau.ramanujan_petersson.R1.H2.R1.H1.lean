import OMAReductions.R_RamanujanTau_ramanujan_petersson_R1_H2_R1
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Reality of the Fourier coefficients of the modular discriminant. -/

open UpperHalfPlane
open scoped ComplexConjugate Topology

private lemma iteratedDeriv_reflection (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n (conj ∘ f ∘ conj) = conj ∘ iteratedDeriv n f ∘ conj := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, deriv_conj_conj, ← iteratedDeriv_succ]

/-- The Euler product is invariant under reflection across the real axis, so
all Taylor coefficients of the discriminant at the cusp are real. -/
private lemma discriminant_coeff_real (n : ℕ) :
    ((qExpansion 1 ModularForm.discriminant).coeff n).im = 0 := by
  let F : ℂ → ℂ := fun q => q * ∏' i : ℕ, (1 - q ^ (i + 1)) ^ 24
  have reflection : conj ∘ F ∘ conj = F := by
    funext z
    change conj (conj z * ∏' i : ℕ, (1 - conj z ^ (i + 1)) ^ 24) = _
    rw [map_mul, Complex.conj_conj]
    have h := Complex.conjCLE.toHomeomorph.isClosedEmbedding.map_tprod
      (L := .unconditional _) (g := (starRingEnd ℂ)) (fun i : ℕ => (1 - conj z ^ (i + 1)) ^ 24)
    simp [F, h]
  have hlocal : cuspFunction 1 ModularForm.discriminant =ᶠ[𝓝 0] F := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
    exact ModularForm.discriminant_cuspFunction_eqOn hz
  have h := congrFun (iteratedDeriv_reflection F n) 0
  rw [reflection] at h
  have hreal : conj (iteratedDeriv n F 0) = iteratedDeriv n F 0 := by
    simpa using h.symm
  apply Complex.conj_eq_iff_im.mp
  rw [qExpansion_coeff, hlocal.iteratedDeriv_eq n]
  simp [hreal]

theorem OMA.solution : OMA.R_RamanujanTau_ramanujan_petersson_R1_H2_R1.H1 := by
  intro p _
  exact discriminant_coeff_real p
