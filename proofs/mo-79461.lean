import OMAStatements.S_mo_79461

open Matrix OMA.S_mo_79461
open scoped ComplexOrder ComplexStarModule MatrixOrder Matrix.Norms.L2Operator

theorem OMA.solution : type_of% @OMA.S_mo_79461.main := by
  intro n
  refine ⟨{A : Mat n | A.PosDef}, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro A hA B hB
    exact Matrix.PosDef.add hA hB
  · intro r hr A hA
    exact Matrix.PosDef.smul hA hr
  · intro A (hA : A.PosDef)
    refine ⟨(posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hA.posSemidef).2, ?_⟩
    let z : ℂ := (hA.isHermitian.eigenvalues 0 : ℝ)
    have hz : z ∈ spectrum ℂ A := by
      rw [hA.isHermitian.spectrum_eq_image_range]
      exact ⟨hA.isHermitian.eigenvalues 0, ⟨0, rfl⟩, rfl⟩
    exact ⟨z, hz, fun he => spectrum.zero_notMem ℂ hA.isUnit (he ▸ hz)⟩
  · intro X
    have hpos (Y : Mat n) (hY : 0 ≤ Y) : (Y + 1).PosDef :=
      Matrix.PosDef.posSemidef_add hY.posSemidef Matrix.PosDef.one
    refine ⟨(ℜ X : Mat n)⁺ + 1, hpos _ (CFC.posPart_nonneg _),
      (ℜ X : Mat n)⁻ + 1, hpos _ (CFC.negPart_nonneg _),
      (ℑ X : Mat n)⁺ + 1, hpos _ (CFC.posPart_nonneg _),
      (ℑ X : Mat n)⁻ + 1, hpos _ (CFC.negPart_nonneg _), ?_⟩
    nth_rw 1 [← CStarAlgebra.linear_combination_nonneg X]
    simp only [smul_add]
    abel
  · intro U heq
    let d (i : Fin (n + 2)) : ℂ := if i = 0 then 1 else 0
    let P : Mat n := diagonal d
    have hP : P ∈ referenceCone n := by
      constructor
      · exact Matrix.PosSemidef.diagonal (fun i => by by_cases hi : i = 0 <;> simp [d, hi])
      · intro h
        have he := congrArg (fun A : Mat n => A 0 0) h
        simp [P, d] at he
    have hd : P.det = 0 := by
      rw [det_diagonal]
      let i : Fin (n + 2) := ⟨1, by omega⟩
      have hi : i ≠ 0 := by intro he; have hv : (1 : ℕ) = 0 := congrArg Fin.val he; omega
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [d, hi])
    have hU : ((U : Mat n) * P * (↑U⁻¹ : Mat n)).PosDef := by
      change _ ∈ {A : Mat n | A.PosDef}
      rw [heq]
      exact Set.mem_image_of_mem _ hP
    have hu := (Matrix.isUnit_iff_isUnit_det _).mp hU.isUnit
    rw [det_mul, det_mul, hd, mul_zero, zero_mul] at hu
    exact not_isUnit_zero hu