import OMAStatements.S_mo_430974
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Matrix

open scoped ComplexOrder

private lemma real_eigenvalue_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (μ : ℝ) :
    Module.End.HasEigenvalue A.toLin' (μ : ℂ) ↔ μ ∈ Set.range hA.eigenvalues := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
  change algebraMap ℝ ℂ μ ∈ spectrum ℂ A ↔ _
  rw [spectrum.algebraMap_mem_iff, hA.spectrum_real_eq_range_eigenvalues]

private lemma row_bound {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℂ}
    {r μ : ℝ} (hd : ∀ i, A i i = 1) (ho : ∀ i j, i ≠ j → ‖A i j‖ ≤ r)
    (hμ : Module.End.HasEigenvalue A.toLin' (μ : ℂ)) : 1 - ((n : ℝ) - 1) * r ≤ μ := by
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hμ
  rw [mem_closedBall_iff_norm', hd, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hi
  have hsum : ∑ j ∈ Finset.univ.erase i, ‖A i j‖ ≤ ((n : ℝ) - 1) * r := calc
    _ ≤ ∑ j ∈ Finset.univ.erase i, r :=
      Finset.sum_le_sum fun j hj => ho i j (Finset.ne_of_mem_erase hj).symm
    _ = _ := by simp [Finset.card_erase_of_mem, Nat.cast_sub (show 1 ≤ n from hn)]
  linarith [(le_abs_self (1 - μ)).trans (hi.trans hsum)]

theorem OMA.solution : type_of% @OMA.S_mo_430974.main := by
  classical
  intro n hn ε hε _
  constructor
  · intro A ⟨hpsd, hd, ho⟩ μ hμ
    obtain ⟨i, hi⟩ := (real_eigenvalue_iff hpsd.isHermitian μ).mp hμ
    exact max_le (hi ▸ hpsd.eigenvalues_nonneg i) (row_bound hn hd ho hμ)
  · have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    obtain ⟨t, ht, htε, hsharp⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ ε ∧
        1 - ((n : ℝ) - 1) * t = max 0 (1 - ((n : ℝ) - 1) * ε) := by
      by_cases h : ((n : ℝ) - 1) * ε ≤ 1
      · exact ⟨ε, hε, le_rfl, (max_eq_right (sub_nonneg.mpr h)).symm⟩
      · have hp : 0 < (n : ℝ) - 1 := by
          by_contra! hz
          rw [le_antisymm hz (sub_nonneg.mpr hn'), zero_mul] at h
          norm_num at h
        refine ⟨1 / ((n : ℝ) - 1), by positivity, (div_le_iff₀ hp).mpr ?_, ?_⟩
        · linarith [mul_comm ε ((n : ℝ) - 1)]
        · rw [max_eq_left (by linarith), mul_one_div_cancel hp.ne']
          ring
    let A : Matrix (Fin n) (Fin n) ℂ := fun i j => if i = j then 1 else -(t : ℂ)
    have hd : ∀ i, A i i = 1 := by simp [A]
    have ho : ∀ i j, i ≠ j → ‖A i j‖ ≤ t := by
      intro i j hij
      simp [A, hij, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    have hH : A.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      by_cases hij : i = j <;> simp [A, hij, eq_comm]
    refine ⟨A, ⟨hH.posSemidef_iff_eigenvalues_nonneg.mpr ?_, hd,
      fun i j hij => (ho i j hij).trans htε⟩, ?_⟩
    · intro i
      have hev := (real_eigenvalue_iff hH (hH.eigenvalues i)).mpr ⟨i, rfl⟩
      exact (le_max_left 0 _).trans (hsharp ▸ row_bound hn hd ho hev)
    · rw [← hsharp]
      apply Module.End.hasEigenvalue_of_hasEigenvector (x := fun _ => (1 : ℂ))
      refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
      · funext i
        change (∑ j, A i j * 1) = _ * 1
        simp only [mul_one]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hd]
        have hoff : ∀ j ∈ Finset.univ.erase i, A i j = -(t : ℂ) := by
          intro j hj
          simp [A, (Finset.ne_of_mem_erase hj).symm]
        rw [Finset.sum_congr rfl hoff]
        simp [Finset.card_erase_of_mem, Nat.cast_sub (show 1 ≤ n from hn)]
        ring
      · intro hz
        exact one_ne_zero (congrFun hz ⟨0, hn⟩)
