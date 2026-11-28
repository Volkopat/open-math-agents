import OMAReductions.R_mo_438166_R1
import Mathlib

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace FiniteResolutionBound
variable {C : Type*} [Category* C] [Abelian C] [EnoughProjectives C]

private theorem resolution_zero_term (n : ℕ) (X : C) (h : HasProjectiveDimensionLT X (n + 1)) :
    ∃ P : ProjectiveResolution X, IsZero (P.complex.X (n + 1)) := by
  induction n generalizing X with
  | zero =>
    have : Projective X := projective_iff_hasProjectiveDimensionLT_one.2 h
    exact ⟨ProjectiveResolution.self X, HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)⟩
  | succ n ih =>
    let p := Projective.π X
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hs : S.ShortExact := { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel p) }
    obtain ⟨P, hP⟩ := ih _ ((hs.hasProjectiveDimensionLT_X₃_iff n (Projective.projective_over X)).1 h)
    let e : P.complex.X 0 ⟶ kernel p := P.π.f 0
    have he : P.complex.d 1 0 ≫ e = 0 := P.complex_d_comp_π_f_zero
    let f := e ≫ kernel.ι p
    have wf : f ≫ p = 0 := (assoc e (kernel.ι p) p).trans (by rw [kernel.condition, comp_zero])
    let K := P.complex.augment f (by change _ ≫ e ≫ _ = 0; rw [← assoc, he, zero_comp])
    let a : K ⟶ (ChainComplex.single₀ C).obj X := (ChainComplex.toSingle₀Equiv K X).symm
      ⟨p, wf⟩
    refine ⟨{ complex := K, π := a, projective := ?_, quasiIso := ⟨?_⟩ }, hP⟩
    · rintro (_ | i)
      · exact Projective.projective_over X
      · exact P.projective i
    · rintro (_ | i)
      · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
        · change (ShortComplex.mk f (a.f 0) _).Exact ∧ Epi (a.f 0)
          have ha : a.f 0 = p := ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
          suffices aux : ∀ (g : Projective.over X ⟶ X) (w : f ≫ g = 0), g = p →
              (ShortComplex.mk f g w).Exact ∧ Epi g from aux _ _ ha
          rintro g w rfl
          let φ : ShortComplex.mk f p wf ⟶ S :=
            { τ₁ := P.π.f 0, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
          have : Epi φ.τ₁ := (inferInstance : Epi (P.π.f 0))
          have : IsIso φ.τ₂ := (inferInstance : IsIso (𝟙 (Projective.over X)))
          have : Mono φ.τ₃ := (inferInstance : Mono (𝟙 X))
          exact ⟨(ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hs.exact, inferInstance⟩
        all_goals rfl
      · rw [quasiIsoAt_iff_exactAt' a _ (ChainComplex.exactAt_succ_single_obj X i),
            HomologicalComplex.exactAt_iff' _ (i+2) (i+1) i (by simp) (by simp)]
        cases i with
        | zero =>
          let φ : ShortComplex.mk _ _ P.complex_d_comp_π_f_zero ⟶ K.sc' 2 1 0 :=
            { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι p
              comm₁₂ := by change 𝟙 _ ≫ P.complex.d 1 0 = _; exact (id_comp _).trans (comp_id _).symm
              comm₂₃ := by exact id_comp f }
          have : Epi φ.τ₁ := (inferInstance : Epi (𝟙 (P.complex.X 1)))
          have : IsIso φ.τ₂ := (inferInstance : IsIso (𝟙 (P.complex.X 0)))
          have : Mono φ.τ₃ := (inferInstance : Mono (kernel.ι p))
          exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 P.exact₀
        | succ i =>
          simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', K,
            ChainComplex.augment_d_succ_succ, ChainComplex.augment_X_succ] using P.exact_succ i

theorem bound {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive]
    (X : C) (n : ℕ) (hn : ¬ IsZero ((F.leftDerived n).obj X)) :
    (n : WithBot ℕ∞) ≤ projectiveDimension X := by
  rw [projectiveDimension_ge_iff]
  intro h
  apply hn
  cases n with
  | zero =>
    have hx := (hasProjectiveDimensionLT_zero_iff_isZero X).1 h
    have : Projective X := hx.projective
    refine IsZero.of_iso ?_ ((ProjectiveResolution.self X).isoLeftDerivedObj F 0)
    erw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero hx)
  | succ n =>
    obtain ⟨P, hP⟩ := resolution_zero_term n X h
    refine IsZero.of_iso ?_ (P.isoLeftDerivedObj F (n+1))
    erw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact ShortComplex.exact_of_isZero_X₂ _ (F.map_isZero hP)

end FiniteResolutionBound

theorem OMA.solution : OMA.R_mo_438166_R1.H3 := by
  intro A D _ _ F _ N n hn
  exact FiniteResolutionBound.bound F N n hn
