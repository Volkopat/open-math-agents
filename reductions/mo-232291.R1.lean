import OMAStatements.S_mo_232291
import Mathlib

-- Credit: @Pixelstorm44

namespace OMA.R_mo_232291_R1

variable {𝕜 : Type} [RCLike 𝕜] {X : Type} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A scalar functional can be tested using its rank-one product with a unit vector. -/
theorem scalar_attainment_of_endomorphisms
    (h : ∀ T : X →L[𝕜] X, ∃ x : X, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖)
    (f : StrongDual 𝕜 X) : ∃ x : X, ‖x‖ = 1 ∧ ‖f x‖ = ‖f‖ := by
  obtain ⟨u, hu, _⟩ := h 0
  obtain ⟨x, hx, he⟩ := h (f.smulRight u)
  refine ⟨x, hx, ?_⟩
  simpa only [ContinuousLinearMap.smulRight_apply, norm_smul, f.norm_smulRight_apply,
    hu, mul_one] using he

/-- Supporting the image of a maximizing vector gives a maximizing functional. -/
theorem normingFunctional_of_attains [Nontrivial X] (T : X →L[𝕜] X)
    {x : X} (hx : ‖x‖ = 1) (he : ‖T x‖ = ‖T‖) : (∃ f : StrongDual 𝕜 X, ‖f‖ = 1 ∧ ‖f.comp T‖ = ‖T‖) := by
  obtain ⟨f, hf, hfx⟩ := exists_dual_vector' 𝕜 (T x)
  refine ⟨f, hf, le_antisymm (by simpa [hf] using f.opNorm_comp_le T) ?_⟩
  have h := (f.comp T).unit_le_opNorm x hx.le
  change ‖f (T x)‖ ≤ _ at h
  simpa only [hfx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), he] using h

/-- Scalar attainment recovers a maximizing vector from a maximizing functional. -/
theorem attains_of_normingFunctional (T : X →L[𝕜] X) (h : (∃ f : StrongDual 𝕜 X, ‖f‖ = 1 ∧ ‖f.comp T‖ = ‖T‖))
    (hs : ∀ g : StrongDual 𝕜 X, ∃ x : X, ‖x‖ = 1 ∧ ‖g x‖ = ‖g‖) :
    ∃ x : X, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ := by
  obtain ⟨f, hf, he⟩ := h
  obtain ⟨x, hx, hg⟩ := hs (f.comp T)
  refine ⟨x, hx, le_antisymm (T.unit_le_opNorm x hx.le) ?_⟩
  calc
    ‖T‖ = ‖(f.comp T) x‖ := (hg.trans he).symm
    _ ≤ ‖f‖ * ‖T x‖ := f.le_opNorm (T x)
    _ = ‖T x‖ := by rw [hf, one_mul]

/-- All compact operators have norm-attaining adjoints, even when their domains
do not have scalar norm attainment. -/
theorem compact_hasNormingFunctional [Nontrivial X] (T : X →L[𝕜] X)
    (hc : IsCompactOperator T) : (∃ f : StrongDual 𝕜 X, ‖f‖ = 1 ∧ ‖f.comp T‖ = ‖T‖) := by
  let B := Metric.closedBall (0 : X) 1
  let K := closure (T '' B)
  have hK : IsCompact K := hc.isCompact_closure_image_closedBall (f := T.toLinearMap) 1
  have hn : K.Nonempty := (Metric.nonempty_closedBall.mpr zero_le_one).image T |>.closure
  obtain ⟨y, hy, hm⟩ := hK.exists_isMaxOn hn continuous_norm.continuousOn
  have hle : ‖T‖ ≤ ‖y‖ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
    intro x hx
    exact hm (subset_closure ⟨x, mem_closedBall_zero_iff.mpr hx.le, rfl⟩)
  obtain ⟨f, hf, hfy⟩ := exists_dual_vector' 𝕜 y
  have hclosed : IsClosed {z : X | ‖f z‖ ≤ ‖f.comp T‖} :=
    isClosed_le f.continuous.norm continuous_const
  have hall : K ⊆ {z : X | ‖f z‖ ≤ ‖f.comp T‖} := by
    apply closure_minimal _ hclosed
    rintro _ ⟨x, hx, rfl⟩
    exact (f.comp T).unit_le_opNorm x (mem_closedBall_zero_iff.mp hx)
  have hyf : ‖f y‖ ≤ ‖f.comp T‖ := hall hy
  rw [hfy, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] at hyf
  exact ⟨f, hf, le_antisymm (by simpa [hf] using f.opNorm_comp_le T) (hle.trans hyf)⟩

/-- The construction step only tests scalar functionals and adjoints of noncompact operators. -/
def H1 : Prop :=
  let candidate := fun (𝕜 : Type) [RCLike 𝕜] =>
    ∃ (X : Type) (norm : NormedAddCommGroup X),
      letI : NormedAddCommGroup X := norm
      ∃ scalars : NormedSpace 𝕜 X,
        letI : NormedSpace 𝕜 X := scalars
        CompleteSpace X ∧ ¬ FiniteDimensional 𝕜 X ∧
          (∀ f : StrongDual 𝕜 X, ∃ x : X, ‖x‖ = 1 ∧ ‖f x‖ = ‖f‖) ∧
          ∀ T : X →L[𝕜] X, ¬ IsCompactOperator T →
            ∃ f : StrongDual 𝕜 X, ‖f‖ = 1 ∧ ‖f.comp T‖ = ‖T‖
  candidate ℝ ∨ candidate ℂ

/-- The compact-operator step is uniform in the scalar field and space. -/
def H2 : Prop := ∀ (𝕜 X : Type) [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [Nontrivial X] (T : X →L[𝕜] X), IsCompactOperator T →
    ∃ f : StrongDual 𝕜 X, ‖f‖ = 1 ∧ ‖f.comp T‖ = ‖T‖

theorem compact_step : H2 := fun _ _ _ _ _ _ T hc => compact_hasNormingFunctional T hc

/-- The tests on a fixed space are also necessary. -/
theorem operator_criterion [Nontrivial X] (hk : H2) :
    (∀ T : X →L[𝕜] X, ∃ x : X, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖) ↔
      (∀ f : StrongDual 𝕜 X, ∃ x : X, ‖x‖ = 1 ∧ ‖f x‖ = ‖f‖) ∧
      ∀ T : X →L[𝕜] X, ¬ IsCompactOperator T →
        ∃ f : StrongDual 𝕜 X, ‖f‖ = 1 ∧ ‖f.comp T‖ = ‖T‖ := by
  constructor
  · intro h
    refine ⟨scalar_attainment_of_endomorphisms h, fun T _ => ?_⟩
    obtain ⟨x, hx, he⟩ := h T
    exact normingFunctional_of_attains T hx he
  · rintro ⟨hs, hn⟩ T
    refine attains_of_normingFunctional T ?_ hs
    by_cases h : IsCompactOperator T
    · exact hk 𝕜 X T h
    · exact hn T h

theorem main : H1 → H2 → type_of% @OMA.S_mo_232291.main := by
  rintro (h | h) hk
  case' inl => left
  case' inr => right
  all_goals
    obtain ⟨X, norm, scalars, hcomplete, hinf, hs, hn⟩ := h
    let := norm
    let := scalars
    obtain ⟨u, hu, _⟩ := hs 0
    have : Nontrivial X := ⟨⟨u, 0, fun h => by simp [h] at hu⟩⟩
    exact ⟨X, norm, scalars, hcomplete, hinf, (operator_criterion hk).mpr ⟨hs, hn⟩⟩

end OMA.R_mo_232291_R1
