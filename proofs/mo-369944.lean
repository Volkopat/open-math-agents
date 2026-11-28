import OMAStatements.S_mo_369944

/-!
Adapted from @amtamaddon’s pending PR #34565, head
35f61203e78b99edea0cc951e826110745c9e07b. The original merged proof is
@AkiRA-COM-FP’s #16035, head 46ef2c1125e854e2415d23d124d6e84bb7d951d5.
The one-sided positivity argument now uses continuity on the closure of (0,1).
The pending construction and its positive-extension contradiction are retained.
-/

theorem OMA.solution : type_of% @OMA.S_mo_369944.main := by
  let f : C(unitInterval, ℝ) := ⟨fun x => (x : ℝ), continuous_subtype_val⟩
  let p : unitInterval := ⟨1/2, by constructor <;> norm_num⟩
  let Φ : C(unitInterval, ℝ) →L[ℝ] ℝ :=
    (4 : ℝ) • ContinuousMap.evalCLM ℝ p - ContinuousMap.evalCLM ℝ (1 : unitInterval)
  have hΦf : Φ f = 1 := by
    simp [Φ, f, p]; norm_num
  have hΦg : Φ (f * f) = 0 := by
    simp [Φ, f, p]; norm_num
  refine ⟨unitInterval, inferInstance, inferInstance, Submodule.span ℝ {f, f * f},
    Φ.comp (Submodule.subtypeL _), ?_, ?_⟩
  · rintro ⟨h, hh⟩ hpos
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hh
    have hL : Φ (a • f + b • (f * f)) = a := by
      rw [map_add, map_smul, map_smul, hΦf, hΦg]; simp
    show 0 ≤ Φ (a • f + b • (f * f))
    rw [hL]
    have hs : Set.Ioo (0:ℝ) 1 ⊆ {x | 0 ≤ a+b*x} := by
      intro x hx
      apply (mul_nonneg_iff_of_pos_right hx.1).mp
      have hp := hpos ⟨x, hx.1.le, hx.2.le⟩
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply,
        ContinuousMap.mul_apply, smul_eq_mul] at hp
      change 0 ≤ a*x+b*(x*x) at hp
      nlinarith
    have hz : (0:ℝ) ∈ closure (Set.Ioo (0:ℝ) 1) := by norm_num [closure_Ioo]
    have := closure_minimal hs (isClosed_le continuous_const (by fun_prop)) hz
    simpa using this
  · rintro ⟨E, hE, hext⟩
    have hf : E f = 1 := by
      have := hext ⟨f, Submodule.subset_span (by simp)⟩
      simpa [hΦf] using this
    have hg : E (f * f) = 0 := by
      have := hext ⟨f * f, Submodule.subset_span (by simp)⟩
      simpa [hΦg] using this
    have key : ∀ t : ℝ, 0 ≤ E 1 - 2 * t * E f + t ^ 2 * E (f * f) := by
      intro t
      have := hE (1 - (2 * t) • f + (t ^ 2) • (f * f)) (by
        intro x
        simp [f]
        nlinarith [sq_nonneg (1 - t * (x : ℝ))])
      simpa [map_sub, map_add, map_smul] using this
    have h0 := key 0
    have h1 := key (E 1 + 1)
    rw [hf, hg] at h0 h1
    nlinarith
