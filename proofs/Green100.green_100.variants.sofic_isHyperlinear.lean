import FormalConjectures.GreensOpenProblems.«100»

/-! Sofic groups are hyperlinear, following @niclorusso (#713).
The permutation embedding uses Mathlib's permutation-matrix homomorphism. -/

namespace OMA.Hyperlinear

/-- The standard permutation-matrix homomorphism. -/
noncomputable abbrev pm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.permMatrixHom (R := ℂ) σ

lemma pm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    pm σ i j = if σ j = i then (1 : ℂ) else 0 := by
  simp [pm, Matrix.permMatrixHom_apply, Equiv.eq_symm_apply, eq_comm]

/-- Permutation matrices give a homomorphism to the unitary group. -/
noncomputable def U {n : ℕ} : Equiv.Perm (Fin n) →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun σ := ⟨pm σ, by
    simp [pm, Matrix.permMatrixHom_apply, Matrix.mem_unitaryGroup_iff,
      Matrix.star_eq_conjTranspose, ← Matrix.permMatrix_mul]⟩
  map_one' := Subtype.ext (map_one (Matrix.permMatrixHom (R := ℂ)))
  map_mul' σ τ := Subtype.ext (map_mul (Matrix.permMatrixHom (R := ℂ)) σ τ)

lemma col_sum {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (j : Fin n) :
    ∑ i, ‖pm σ i j - pm τ i j‖ ^ 2 = if σ j = τ j then (0 : ℝ) else 2 := by
  by_cases h : σ j = τ j
  · rw [if_pos h]
    simp [pm_apply, h]
  · rw [if_neg h]
    have key : ∀ i, ‖pm σ i j - pm τ i j‖ ^ 2 =
        (if σ j = i then (1 : ℝ) else 0) + (if τ j = i then (1 : ℝ) else 0) := by
      intro i
      by_cases h1 : σ j = i
      · by_cases h2 : τ j = i
        · exact absurd (h1.trans h2.symm) h
        · simp [pm_apply, h1, h2]
      · by_cases h2 : τ j = i
        · simp [pm_apply, h1, h2]
        · simp [pm_apply, h1, h2]
    rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    norm_num

lemma sum_sq {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    ∑ i, ∑ j, ‖pm σ i j - pm τ i j‖ ^ 2 = 2 * (hammingDist ⇑σ ⇑τ : ℝ) := by
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun j _ => col_sum σ τ j)]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul,
    mul_comm]
  rfl

lemma hsDist_U {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    Green100.hsDist (U σ) (U τ) = Real.sqrt (2 * Green100.hammingDistNorm σ τ) := by
  unfold Green100.hsDist Green100.hammingDistNorm
  change Real.sqrt ((∑ i, ∑ j, ‖pm σ i j - pm τ i j‖ ^ 2) / n) = _
  rw [sum_sq, mul_div_assoc]

lemma hdn_nonneg {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : 0 ≤ Green100.hammingDistNorm σ τ := by
  unfold Green100.hammingDistNorm
  positivity

lemma hsDist_U_lt {n : ℕ} (σ τ : Equiv.Perm (Fin n)) {ε : ℝ} (hε : 0 < ε)
    (h : Green100.hammingDistNorm σ τ < ε ^ 2 / 2) : Green100.hsDist (U σ) (U τ) < ε := by
  rw [hsDist_U]
  have h0 := hdn_nonneg σ τ
  calc Real.sqrt (2 * Green100.hammingDistNorm σ τ) < Real.sqrt (ε ^ 2) :=
        Real.sqrt_lt_sqrt (by positivity) (by linarith)
    _ = ε := Real.sqrt_sq hε.le

lemma hsDist_U_ge {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (h : (1 / 4 : ℝ) ≤ Green100.hammingDistNorm σ τ) :
    (1 / 4 : ℝ) ≤ Green100.hsDist (U σ) (U τ) := by
  rw [hsDist_U, Real.le_sqrt (by norm_num) (by linarith)]
  nlinarith

end OMA.Hyperlinear

open OMA.Hyperlinear in
theorem OMA.solution : type_of% @Green100.green_100.variants.sofic_isHyperlinear := by
  intro G _ hG
  unfold Green100.IsSofic at hG
  unfold Green100.IsHyperlinear
  intro F ε hε
  obtain ⟨n, θ, h1, h2, h3⟩ := hG F (ε ^ 2 / 2) (by positivity)
  refine ⟨n, fun g => U (θ g), ?_, ?_, ?_⟩
  · intro g hg h hh hgh
    show Green100.hsDist (U (θ g) * U (θ h)) (U (θ (g * h))) < ε
    rw [← map_mul]
    exact hsDist_U_lt _ _ hε (h1 g hg h hh hgh)
  · intro h1F
    show Green100.hsDist (U (θ 1)) 1 < ε
    rw [← map_one U]
    exact hsDist_U_lt _ _ hε (h2 h1F)
  · intro x hx y hy hxy
    exact hsDist_U_ge _ _ (h3 x hx y hy hxy)
